/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import AdalyFormal.Migration.L8c
import AdalyFormal.Balaban.AdmissibleSubspace

/-!
# The coercivity operator `Δ_k(U)` — statement shape only

Phase-0 REFORM_PROGRAM definitions layer, `PHASE0_DEFS_PLAN.md` item **B2**. Stands alone (plus
`Migration.L8c`, added by this R3 correction so the "composes directly" claim below is a
kernel-checked theorem, not prose — see §3).

## R3 CORRECTION (2026-07-21) — statement-rigging repair, `SOL_GATE_COERCIVITY_AND_RENAME.md`

The R2 shape (subspace-restricted `coercive`, `V : Submodule ℝ H` a bare field) was CONVICTED by a
de-correlated Sol prosecution (`compute/SOL_GATE_COERCIVITY_AND_RENAME.md` §2, confirmed
independently by the main loop from scratch before this dispatch fired): `Nonempty
(CoercivityHypothesis H Uconfig)` — the EXACT type `Spine.coerc_u_main` states for `[LEM-COERC-U]`,
the campaign's hardest open crux — was inhabited by `Δ := 0`, `V := ⊥`, `γ'' := 1`, for ARBITRARY
`H`/`Uconfig`, no mathematics required (`botZeroCoercivityAnyU`,
`compute/.sol_logs/coercivity_rename_gate/CoercivityAudit.lean`). Three further findings in the
same report: (i) `hVne : V ≠ ⊥` was an ARGUMENT of `Probes.zeroCoercivity_blocked`, not a FIELD of
`CoercivityHypothesis` — it guarded one theorem about an already-built structure, not construction
of the structure; (ii) the claimed "composes with `Migration.L8c.perturbation_transfer` without an
adapter" was FALSE — `Δ : ℕ → Uconfig → H →ₗ[ℝ] H` (`LinearMap`) does not unify with L8c's
`H →L[ℝ] H` (`ContinuousLinearMap`), Sol made the direct application fail with a pasted type error;
(iii) `ofUnrestricted_coercive_of_top` proved equality of two PROOFS of the same proposition — a
`Subsingleton.elim`-forced check (S82), not a data-level round trip.

This correction addresses all three, and reports — rather than papers over — the residual that
survives it (see §4, "what this correction does NOT close").

### §1 — `Δ`'s type: `H →L[ℝ] H`, matching `L8c` exactly

Fixes (ii). `Δ` is now `ℕ → Uconfig → H →L[ℝ] H` throughout. §3 below ships
`CoercivityHypothesis.composes_with_L8c`, a THEOREM applying `Migration.L8c.perturbation_transfer`
to `h.Δ k U₁`/`h.Δ k U₂` with **no coercion, no `.toContinuousLinearMap`, no adapter of any kind** —
closing the exact gap Sol's pasted type error exhibited.

### §2 — `V ≠ ⊥` and `Δ` genuinely `U`-dependent: now STRUCTURE FIELDS, not caller hypotheses

Fixes (i), and goes further. Two new fields:

* **`V_ne_bot : V ≠ ⊥`.** Was `Probes.zeroCoercivity_blocked`'s external `hVne` argument (guards a
  theorem about an already-built instance); now every TERM of `CoercivityHypothesis H Uconfig`
  carries this proof intrinsically — there is no longer a hypothesis for a downstream consumer to
  omit. `botZero_no_longer_inhabits` below reconstructs Sol's exact `(Δ,V) = (0,⊥)` pair and derives
  `False` directly from the field, and the general fact `CoercivityHypothesis.V_ne_bot_always`
  subsumes it for ANY `Δ`.
* **`Δ_nonconstant`, plus `[Nontrivial Uconfig]` on the structure itself.** `[LEM-COERC-U]`'s own
  name is "coercivity general in `U`" — the crux is that `Δ_k(U)` genuinely VARIES with the gauge
  configuration `U` while the lower bound stays uniform. A `Uconfig := PUnit` instance (Sol's
  `restrictedOnlyCoercivity`, `Balaban/Probes.lean`) or a `Δ` that ignores `U` trivially "solves"
  uniformity for a reason that has nothing to do with the mathematics. `[Nontrivial Uconfig]` (an
  instance argument of the structure, so `CoercivityHypothesis H PUnit` no longer even
  TYPECHECKS — `punit_not_nontrivial` below) plus `Δ_nonconstant : ∃ k U₁ U₂, U₁ ≠ U₂ ∧
  Δ k U₁ ≠ Δ k U₂` (Δ must actually differ somewhere) together block Sol's EXACT
  `restrictedOnlyCoercivity` witness — `punit_not_nontrivial` below shows its `Uconfig := PUnit`
  no longer even typechecks; `positiveLine_generalized_survives` (§4/§5) is the honest report on
  what a GENERALIZED version of the same attack still does NOT block.

**Consequence for the rest of the tree, reported for the wiring lane (`Spine.lean` is out of this
file's write-scope):** every `[Nonempty Uconfig]` hypothesis touching `Balaban.CoercivityHypothesis`
(`Spine.lean`'s `coerc_u_main`, `gap1_main`, `gap2_main`, `gap3_ladder_massGap`, `main`) must become
`[Nontrivial Uconfig]` — `Nontrivial` implies `Nonempty` so this is a strict strengthening, not a
weakening, matching `REFORM_PROGRAM.md` L5 ("harder to inhabit is the correct outcome"). The exact
new statement `coerc_u_main` must carry:
```
theorem coerc_u_main [Nontrivial Uconfig] :
    Nonempty (Balaban.CoercivityHypothesis H Uconfig) := by
  sorry
```

### §3 — the data-level round trip (fixes iii)

`CoercivityHypothesis.ofUnrestricted_data_roundtrip` below replaces the CONVICTED
`ofUnrestricted_coercive_of_top`: it asserts equality of the actual `Δ`/`γ''` DATA recovered by
`ofUnrestricted`, not equality of two proofs of the same inequality. `Δ : ℕ → Uconfig → H →L[ℝ] H`
is `Type`-valued, so `.Δ = Δ` is NOT automatically forced by proof irrelevance — it is genuinely
informative (only true because `ofUnrestricted` literally sets the field to `Δ`).

### §4 — what this correction does NOT close (read before citing this file as "repaired")

**Reconstructed and refuted, honestly, in §5 below**: §2's fix blocks Sol's TWO EXACT witnesses
(the `(0,⊥)` pair and the `PUnit`-`Uconfig` `restrictedOnlyCoercivity` term). It does **not** close
the underlying FAMILY of attacks. `positiveLine_generalized_survives` below constructs a
`CoercivityHypothesis CheapWitnessSpace Bool` instance — `Uconfig := Bool` (genuinely `Nontrivial`),
`Δ k true := c₁ • P_V`, `Δ k false := c₂ • P_V` for `c₁ ≠ c₂`, both `> 0` — that satisfies EVERY
field of the R3-repaired structure, including `V_ne_bot` and `Δ_nonconstant`, while being exactly
as source-unanchored as Sol's original: it is still a scaled orthogonal projection onto a `V`
chosen freely by the term, not the campaign's actual `Δ_k(U)` or CMP96 `(2.121)`'s admissible
subspace.

**Why no further "soft" field (self-adjointness, global boundedness, an upper bound matching the
lower bound, non-vanishing off `V`, ...) can close this without anchoring**: `H`, `Δ`, `V`, `γ''`
are abstract Hilbert-space data with no property tying them to `Blocks.lean`'s `BlockGeometry`,
CMP96's bond space, or `(2.121)`'s axis-anchored `Γ_{y,x}` path set. For ANY such internal
property `P`, if the real Balaban `(Δ_k(U), V)` pair satisfies `P` (as it must, to keep the
target provable-in-principle), a sufficiently rich toy construction built purely from `V` and one
or more real scalars can typically be tuned to satisfy `P` too — `positiveLine_generalized_
survives` demonstrates this for the two fields THIS correction adds; `Δ`'s own docstring
(`RestrictionWitnessSpace`, formerly in `Probes.lean`) already demonstrated it for
self-adjointness (`obliqueQCLM`-style tricks are unnecessary here — `c • P_V` is ALREADY
self-adjoint). **Genuine closure requires anchoring `Δ` and `V` to the actual source construction**
— `Balaban.BlockGeometry`'s own docstring: "does NOT commit to a specific embedding ... the module
does not attempt to name `Γ_{y,x}` itself (that is `Blocks.lean`/`Lattice/` territory, out of this
file's scope)". No `Lattice/` directory and no `Δ_k(U)` operator construction exist anywhere in
this Lean tree (confirmed by direct inspection of `Blocks.lean`, `ScaleLadder.lean`,
`Averaging.lean`, `IteratedAveraging.lean`: all combinatorial/`Finset`-typed, no Hilbert space `H`,
no operator anywhere). **This is the named blocker**: `[LEM-COERC-U]` cannot be fully statement-
repaired against arbitrary-positive-line attacks until `Γ_{y,x}` and `Δ_k(U)` are built — a
DIFFERENT lane's Phase-0 deliverable, not invented here per the direct mandate ("a named blocker
beats a wrong encoding").

**STATUS UPDATE 2026-07-21 — the paragraph above is now PARTLY STALE. Read this before relying on
it.**
* **`Γ_{y,x}` HAS been built** — `Balaban/AdmissibleSubspace.lean`, a genuine `Submodule` from
  lattice geometry. **But it is CONVICTED** by a de-correlated gate
  (`compute/SOL_GATE_ADMISSIBLE_SUBSPACE.md`) on two counts: the coordinate order is probably
  **inverted** (p.244's telescope selects what that file ships as `reverseStaircasePath`), and the
  subspace **does not consume the block geometry at all** — no `ell`, no `x ∈ B(y)`, no `y ∈ Λ'`.
  A repair lane is settling the orientation against the page image.
* **Wiring it in changed nothing measurable**: anchoring `V` killed **0 of 9** attacks in the
  standing S91 regression suite (`COERCIVITY_ANCHORING.md`), because `Δ` remains free and no field
  ties its functional form to the anchored `V`.
* **`Δ_k(U)` is still unbuilt, but is NO LONGER open mathematics.** `RG_LINEARIZATION.md` located
  its actual definition on printed p.243 — `⟨B,Δ_jB⟩ := ⟨H_jB,(Δ-∂P_j∂*)H_jB⟩ = ‖∂H_jB‖²`, a
  **Schur-complement / effective-covariance operator from a constrained Gaussian integral**, *not*
  a second variation of the averaging map as this file and others previously guessed. Its
  dependency chain (`Q`, `R`, `P`, `Δ_a`, `G`, `H_j`) is mapped, and the positivity result it rests
  on is CMP89 — **already in this corpus**. It is a formalization debt, not unsolved mathematics.
* Note also that p.243's `Δ_j` carries **no explicit `U`-dependence**; the `U`-dependent
  generalization `[LEM-COERC-U]` needs likely comes from a later background-field paper.

**Independently re-rendered and read for THIS correction** (LAW-11/20; not a re-use of Sol's
render — a fresh `pdftoppm -r 300 -f 22 -l 22` on the same PDF, sha256
`07ab9fee9e3858b252fb3a1a51c6d17457aa1c5b93b1358d05234acef310688c`, BYTE-IDENTICAL to Sol's pinned
hash, confirming both the offset (`corpus/tools/page_offsets.json`, `CMP96` offset 222 ⇒ printed
p.244 = PDF page 22) and the reading below): CMP96 printed p.244 states **(2.120)** as the WHOLE
three-term form `‖B↾_{Λᶜ}‖² + L⁻²‖(Q₁B)↾_{Λ′}‖² + ⟨B, Δ_jB⟩`, restricted to configurations `B`
satisfying **(2.121)** `B(b) = 0` for `b ⊂ Γ_{y,x}`, `x ∈ B(y)`, `y ∈ Λ′` (axis-anchored,
direction-asymmetric — a specific bond set tied to specific `x, y`, never a symmetrized ball); the
text then explicitly REPLACES the `⟨B,Δ_jB⟩` term via bound (2.118) to form **(2.122)**
`‖B↾_{Λᶜ}‖² + L⁻²‖(Q₁B)↾_{Λ′}‖² + γ₀‖∂₁B‖²` — note `Δ_j` does **not even appear** in (2.122); it was
already absorbed into the `γ₀‖∂₁B‖²` term — and states "We will prove that it is bounded from below
by `γ₀″‖B‖²`" for THIS WHOLE THREE-TERM FORM, on configurations satisfying (2.121). **This file's
`coercive` field (`γ'' * ‖v‖² ≤ ⟨v, Δ v⟩`, a bare bilinear form) remains a NAMED, DISCLOSED
SIMPLIFICATION relative to (2.122)'s actual three-term sum, not a literal transcription of it** —
correcting the R2 module docstring, which described (2.122) as though it bounded `⟨B,Δ_jB⟩` alone.
Building the faithful three-term form requires `Λᶜ`-restriction, `Q₁`, and `∂₁` — lattice
differential/averaging operators with no Lean construction anywhere in this tree — the SAME named
blocker as above, not fixed by this correction.

## Why statement-shape only, no construction, no witness FOR `[LEM-COERC-U]` ITSELF

`PHASE0_DEFS_PLAN.md` §3, item B2, is explicit: *"a `Prop`/hypothesis shape only, NOT a
construction (the construction is exactly `RESIDUAL_REGISTER.md`'s `[LEM-COERC-U]`, which is open
mathematics in the Python campaign right now)... cannot yet be named [a witness] — this is exactly
why B2 must stay a bare hypothesis/`sorry` shape in `Spine.lean` rather than a `def` with a
witness. Naming a witness here would mean exhibiting an operator satisfying `[LEM-COERC-U]`, which
is the open mathematics itself."* This module respects that line: `CoercivityHypothesis` below is a
`structure` whose fields state the REQUIRED positivity shape; **no instance of it is constructed for
the campaign's actual `Δ_k(U)` (arbitrary gauge configuration `U`, the general-`U` case), anywhere
in this file**, and none should be until `[LEM-COERC-U]` itself is closed. §5's witnesses are, as
before, SHAPE witnesses and degenerate-witness prosecutions — never claims to solve the open
mathematics, and `positiveLine_generalized_survives` is explicitly the opposite of a solution: a
disclosed, honest demonstration of what remains unclosed.
-/

namespace AdalyFormal.Balaban

/-- **Statement shape of `[LEM-COERC-U]`, R3-corrected.** A family of self-adjoint-shaped positive
operators `Δ : (k : ℕ) → U → H →L[ℝ] H` (a `ContinuousLinearMap`, matching `Migration.
L8c.perturbation_transfer`'s convention EXACTLY — §1) on a real inner-product space `H`, bounded
below by a UNIFORM (in both `k` and the gauge configuration `U`) constant `γ'' > 0`, on a
distinguished subspace `V` (CMP96 `(2.121)`'s codimension restriction) that is REQUIRED to be
nontrivial (`V_ne_bot`, §2 — was an external hypothesis, `Probes.zeroCoercivity_blocked`'s `hVne`;
now intrinsic to every instance) over a genuinely NONTRIVIAL, `Δ`-discriminating configuration
space (`[Nontrivial Uconfig]` plus `Δ_nonconstant`, §2 — `[LEM-COERC-U]`'s own point is uniformity
DESPITE genuine `U`-dependence, so a `U`-independent or `Uconfig`-trivial witness proves nothing
about it). **No instance of this structure is constructed for the general-`U` case in this file** —
module docstring above; §5's witnesses are for the SHAPE only, and §4/§5 disclose exactly what
remains open even after this correction. -/
structure CoercivityHypothesis (H : Type*) (Uconfig : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig] where
  /-- The operator family, one per scale `k` and gauge configuration `U` — a `ContinuousLinearMap`
  (§1 R3 correction), matching `Migration.L8c.perturbation_transfer`'s `H →L[ℝ] H` exactly, so the
  two compose with NO adapter (`composes_with_L8c` below, §3). -/
  Δ : ℕ → Uconfig → H →L[ℝ] H
  /-- The distinguished subspace CMP96 `(2.121)` restricts to — `⊤` (the whole space) for Gap 1's
  genuinely torus-only case; a proper subspace for Gap 2 / Gap 3's ladder P5 / FRD `[I1]`
  (`RESIDUAL_REGISTER.md` Tier 1 / Tier C.1). A `Submodule`, not a `Set`, because `(2.121)`'s own
  defining condition `B(b) = 0` on a fixed bond set is linear. -/
  V : Submodule ℝ H
  /-- **R3 correction, §2**: `V ≠ ⊥` is now a FIELD, not a downstream theorem's hypothesis. A
  vacuous `V = ⊥` bound would be satisfiable by the zero operator and prove nothing (`Probes.
  zeroOperator_admissible_at_bot`, still valid against the OLD R2 shape) — `botZero_no_longer_
  inhabits` below shows this specific exploit no longer has a term of the corrected type at all. -/
  V_ne_bot : V ≠ ⊥
  /-- **R3 correction, §2**: `Δ` genuinely depends on `U` — at some scale `k`, at least two
  distinct configurations `U₁ ≠ U₂` give DIFFERENT operators. `[LEM-COERC-U]`'s content is
  uniformity DESPITE this variation; a `U`-independent `Δ` (Sol's `restrictedOnlyCoercivity`,
  `Balaban/Probes.lean`) trivializes the question it is meant to answer. Paired with
  `[Nontrivial Uconfig]` on the structure itself (so `Uconfig := PUnit` does not even typecheck),
  this blocks Sol's exact witness (`punit_not_nontrivial` below) — see `positiveLine_generalized_
  survives` (§4/§5) for the honest report on what a GENERALIZED version of it does NOT block. -/
  Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂
  /-- The uniform lower bound, matching CMP96 p.244's `γ₀''`. -/
  γ'' : ℝ
  /-- The bound is strictly positive. -/
  γ''_pos : 0 < γ''
  /-- The coercivity bound itself, a NAMED SIMPLIFICATION of CMP96 `(2.122)`'s shape (§4: the page
  bounds the WHOLE three-term form, not this bare bilinear form, below by `γ₀''‖B‖²`) — uniform in
  `k` and `U`, restricted to `v ∈ V`. -/
  coercive : ∀ (k : ℕ) (U : Uconfig), ∀ v ∈ V, γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v)

/-- **Torus specialization (Gap 1's own case, preserved).** When the subspace is the whole space
(`V = ⊤` — Gap 1 is genuinely torus-only/unrestricted), `coercive` recovers the plain unrestricted
bound on every `v : H`, exactly what Gap 1's consumer needs. -/
theorem CoercivityHypothesis.coercive_of_top {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig]
    (h : CoercivityHypothesis H Uconfig) (hV : h.V = ⊤) :
    ∀ (k : ℕ) (U : Uconfig) (v : H), h.γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (h.Δ k U v) :=
  fun k U v => h.coercive k U v (hV ▸ Submodule.mem_top)

/-- **Torus constructor, the exact inverse direction (R3-updated signature: `Δ_nonconstant` is now
a required argument, matching the structure's new field; `[Nontrivial H]` is required so `⊤ ≠ ⊥`
can be discharged for `V_ne_bot`).** Builds a `V = ⊤` `CoercivityHypothesis` directly from
unrestricted, genuinely `U`-varying data. -/
def CoercivityHypothesis.ofUnrestricted {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [Nontrivial Uconfig]
    (Δ : ℕ → Uconfig → H →L[ℝ] H) (γ'' : ℝ) (γ''_pos : 0 < γ'')
    (coercive : ∀ (k : ℕ) (U : Uconfig) (v : H), γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v))
    (Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂) :
    CoercivityHypothesis H Uconfig where
  Δ := Δ
  V := ⊤
  V_ne_bot := (bot_lt_top (α := Submodule ℝ H)).ne'
  Δ_nonconstant := Δ_nonconstant
  γ'' := γ''
  γ''_pos := γ''_pos
  coercive := fun k U v _ => coercive k U v

@[simp] theorem CoercivityHypothesis.ofUnrestricted_V {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [Nontrivial Uconfig]
    (Δ : ℕ → Uconfig → H →L[ℝ] H) (γ'' : ℝ) (γ''_pos : 0 < γ'')
    (coercive : ∀ (k : ℕ) (U : Uconfig) (v : H), γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v))
    (Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂) :
    (CoercivityHypothesis.ofUnrestricted Δ γ'' γ''_pos coercive Δ_nonconstant).V = ⊤ := rfl

/-- **§3 — the round trip, on the DATA, replacing the CONVICTED `ofUnrestricted_coercive_of_top`
(R2, `SOL_GATE_COERCIVITY_AND_RENAME.md` §2.4: that theorem proved equality of two PROOFS of the
same proposition — `Subsingleton.elim`-forced, S82, not evidence of a genuine inverse
construction).** `Δ : ℕ → Uconfig → H →L[ℝ] H` and `γ'' : ℝ` are `Type`-valued data, NOT
propositions: `.Δ = Δ` and `.γ'' = γ''` are not automatically true of any two constructions with
matching TYPES, only of ones that literally return the same values — genuinely informative,
unlike the old proof-equality. -/
theorem CoercivityHypothesis.ofUnrestricted_data_roundtrip {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [Nontrivial Uconfig]
    (Δ : ℕ → Uconfig → H →L[ℝ] H) (γ'' : ℝ) (γ''_pos : 0 < γ'')
    (coercive : ∀ (k : ℕ) (U : Uconfig) (v : H), γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v))
    (Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂) :
    (CoercivityHypothesis.ofUnrestricted Δ γ'' γ''_pos coercive Δ_nonconstant).Δ = Δ
      ∧ (CoercivityHypothesis.ofUnrestricted Δ γ'' γ''_pos coercive Δ_nonconstant).γ'' = γ'' :=
  ⟨rfl, rfl⟩

/-! ## §3 (continued) — L8c compatibility, DEMONSTRATED, not merely claimed -/

/-- **The claim Sol made fail is now a kernel-checked theorem.** `h.Δ k U₁`, `h.Δ k U₂` are
`H →L[ℝ] H` — EXACTLY `Migration.L8c.perturbation_transfer`'s operator type — so this composes with
**no `.toContinuousLinearMap`, no coercion, no adapter of any kind**, unlike the R2 shape (§1 R3
correction; `SOL_GATE_COERCIVITY_AND_RENAME.md` §2.3 pasted the exact type error the R2 shape
produced here). -/
theorem CoercivityHypothesis.composes_with_L8c {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [Nontrivial Uconfig]
    (h : CoercivityHypothesis H Uconfig) [h.V.HasOrthogonalProjection]
    (k : ℕ) (U₁ U₂ : Uconfig) (ε : ℝ)
    (hE : ‖h.V.starProjection ∘L ((h.Δ k U₂ - h.Δ k U₁) ∘L h.V.starProjection)‖ ≤ ε) :
    ∀ B ∈ h.V, (h.γ'' - ε) * ‖B‖ ^ 2 ≤ inner ℝ B (h.Δ k U₂ B) :=
  Migration.L8c.perturbation_transfer h.V (h.Δ k U₁) (h.Δ k U₂) h.γ'' ε (h.coercive k U₁) hE

/-! ## §5 — degenerate-witness prosecution (OPS-1: "a residual must be EARNED"; both the CLOSED
half — (a), Sol's exact `(0,⊥)` witness — and the SURVIVING half — (b)'s honest generalization —
are shipped here, kernel-checked, not asserted in prose.) -/

/-- **(a), general form.** ANY term of the R3-corrected `CoercivityHypothesis` already carries
`V ≠ ⊥` — restated as a standalone fact so downstream files can cite it without unpacking the
structure. -/
theorem CoercivityHypothesis.V_ne_bot_always {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig]
    (h : CoercivityHypothesis H Uconfig) : h.V ≠ ⊥ := h.V_ne_bot

/-- **(a), Sol's EXACT historical exploit, reconstructed and refuted at the same granularity.**
`botZeroCoercivityAnyU` (`compute/.sol_logs/coercivity_rename_gate/CoercivityAudit.lean`): `Δ := 0`,
`V := ⊥`, for ARBITRARY `H`, `Uconfig`. No such pair can inhabit the R3-corrected structure. -/
theorem botZero_no_longer_inhabits {H Uconfig : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig] :
    ¬ ∃ (h : CoercivityHypothesis H Uconfig), (∀ k U, h.Δ k U = 0) ∧ h.V = ⊥ := by
  rintro ⟨h, -, hVbot⟩
  exact h.V_ne_bot hVbot

/-- **(b), first half: Sol's exact `restrictedOnlyCoercivity` witness no longer TYPECHECKS.** That
witness (`Balaban/Probes.lean`) used `Uconfig := PUnit`. `PUnit` is a subsingleton: `Nontrivial
PUnit` — now REQUIRED just to STATE `CoercivityHypothesis H PUnit`, since `Nontrivial Uconfig` is
an instance argument of the structure itself — has no instance. This is a proof that the witness's
TYPE is no longer well-formed, not merely that its content is disallowed. -/
theorem punit_not_nontrivial : ¬ Nontrivial PUnit := by
  rintro ⟨a, b, hab⟩
  exact hab (Subsingleton.elim a b)

noncomputable section HonestResidual

/-! ## §5 (continued) — `(b)`, the FULL honest report: the underlying attack family survives

`punit_not_nontrivial` blocks Sol's LITERAL witness term. It does NOT close `[LEM-COERC-U]`'s
target: the family "a scaled orthogonal projection onto a freely-chosen `V`" survives with one more
line of work (make it vary across `Uconfig`). This is shipped, not hidden — see the module
docstring §4 for why no further internal/soft field can close this without anchoring `Δ`, `V` to
`Balaban.BlockGeometry`'s `Γ_{y,x}`/`Δ_k(U)`, neither of which exist in this tree. -/

/-- The witness ambient space, reusing `Migration.L8c`'s / `Balaban.Probes`' own convention. -/
abbrev CheapWitnessSpace : Type := EuclideanSpace ℝ (Fin 2)

/-- A genuine PROPER, NONTRIVIAL subspace, freely chosen — exactly as Sol's `RestrictionWitnessV`
was, and exactly the freedom `(2.121)`'s axis-anchored `Γ_{y,x}` subspace is supposed to remove
once it is actually constructed (it is not, in this tree — the named blocker, §4). -/
def CheapWitnessV : Submodule ℝ CheapWitnessSpace :=
  Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}

theorem cheapWitnessV_ne_bot : CheapWitnessV ≠ ⊥ := by
  simp only [CheapWitnessV, ne_eq, Submodule.span_singleton_eq_bot]
  simp

/-- **The `U`-varying scaled-projector family** — the minimal extra work needed to survive the R3
`Δ_nonconstant` field: `c₁ • P_V` at `U = true`, `c₂ • P_V` at `U = false`, `c₁ ≠ c₂`, both `> 0`.
Still a bare function of `V` alone; still exactly as source-unanchored as Sol's original.
(`cond`, not `if U then _ else _`: the latter desugars to `ite (U = true) _ _` for `U : Bool`,
whose reduction after `cases`/substitution is one `decide` step away from the `rfl`-simp lemmas
`cond_true`/`cond_false` — using `cond` directly keeps the witness proofs first-order.) -/
def cheapWitnessΔ (c₁ c₂ : ℝ) : ℕ → Bool → CheapWitnessSpace →L[ℝ] CheapWitnessSpace :=
  fun _ U => (cond U c₁ c₂) • CheapWitnessV.starProjection

theorem cheapWitness_coercive (c₁ c₂ : ℝ) (_h1 : 0 < c₁) (_h2 : 0 < c₂) :
    ∀ (k : ℕ) (U : Bool), ∀ v ∈ CheapWitnessV,
      (min c₁ c₂) * ‖v‖ ^ 2 ≤ inner ℝ v (cheapWitnessΔ c₁ c₂ k U v) := by
  intro k U v hv
  have hPv : CheapWitnessV.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hnn : (0:ℝ) ≤ ‖v‖ ^ 2 := by positivity
  cases U with
  | true =>
    simp only [cheapWitnessΔ, cond_true, smul_apply, hPv]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hnn
  | false =>
    simp only [cheapWitnessΔ, cond_false, smul_apply, hPv]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hnn

theorem cheapWitness_nonconstant (c₁ c₂ : ℝ) (hne : c₁ ≠ c₂) :
    cheapWitnessΔ c₁ c₂ 0 true ≠ cheapWitnessΔ c₁ c₂ 0 false := by
  intro hcontra
  have heval := DFunLike.congr_fun hcontra (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  simp only [cheapWitnessΔ, cond_true, cond_false, smul_apply] at heval
  have hPe : CheapWitnessV.starProjection (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _)
  rw [hPe] at heval
  have hne0 : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ≠ 0 := by simp
  have hsub : (c₁ - c₂) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = 0 := by
    rw [sub_smul, heval, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact hne (sub_eq_zero.mp h)
  · exact hne0 h

/-- **`(b)`, the honest finding, as a kernel-checked term.** A full, genuine
`CoercivityHypothesis CheapWitnessSpace Bool` instance — every field present, including the two
this correction ADDED (`V_ne_bot`, `Δ_nonconstant`) — built from nothing but a freely-chosen
nontrivial `V` and two distinct positive scalars. `Uconfig := Bool` is genuinely `Nontrivial`
(unlike Sol's `PUnit`), and `Δ` genuinely varies across it. This is NOT a witness for
`[LEM-COERC-U]` (module docstring: no instance for the general-`U` case is claimed to solve the
open mathematics) — it is the disclosed demonstration that the R3 fields, while blocking the two
EXACT exploits found so far, do not by themselves rule out the whole FAMILY of positive-line
attacks. -/
noncomputable def positiveLine_generalized_survives (c₁ c₂ : ℝ) (h1 : 0 < c₁) (h2 : 0 < c₂)
    (hne : c₁ ≠ c₂) : CoercivityHypothesis CheapWitnessSpace Bool where
  Δ := cheapWitnessΔ c₁ c₂
  V := CheapWitnessV
  V_ne_bot := cheapWitnessV_ne_bot
  Δ_nonconstant := ⟨0, true, false, by decide, cheapWitness_nonconstant c₁ c₂ hne⟩
  γ'' := min c₁ c₂
  γ''_pos := lt_min h1 h2
  coercive := cheapWitness_coercive c₁ c₂ h1 h2

/-- **Non-vacuity of the honest-residual instance itself** — confirms
`positiveLine_generalized_survives` is a genuine, non-degenerate term (nonzero witness vector,
strictly positive bound), not accidentally rejected by its own type. -/
theorem positiveLine_generalized_survives_nontrivial (c₁ c₂ : ℝ) (h1 : 0 < c₁) (h2 : 0 < c₂)
    (hne : c₁ ≠ c₂) :
    Nonempty (CoercivityHypothesis CheapWitnessSpace Bool)
      ∧ (positiveLine_generalized_survives c₁ c₂ h1 h2 hne).V ≠ ⊥
      ∧ 0 < (positiveLine_generalized_survives c₁ c₂ h1 h2 hne).γ'' :=
  ⟨⟨positiveLine_generalized_survives c₁ c₂ h1 h2 hne⟩, cheapWitnessV_ne_bot, lt_min h1 h2⟩

end HonestResidual

/-! ## §6 — THE ANCHORING (this dispatch, 2026-07-21)

`ADMISSIBLE_SUBSPACE.md` / `COERCIVITY_STATEMENT_REPAIR.md` §4's named blocker: `V` above is a bare
FIELD, freely chosen by whoever builds a `CoercivityHypothesis` term — `positiveLine_generalized_
survives` (§5 above) is the disclosed proof that this freedom is real and exploitable. `Balaban.
AdmissibleSubspace.admissibleSubspace y x` (a companion, concurrently-landed module, NO-GO for this
dispatch to edit — consumed here per LAW-19) is CMP96 `(2.121)`'s `Γ_{y,x}`-defined subspace,
genuinely derived from lattice geometry, not a free parameter. This section promotes it to a
`Submodule` of an actual `InnerProductSpace` (`AdmissibleSubspace.admissibleSubspace` lives on the
bare Pi type `Bond L → ℝ`, which carries no `InnerProductSpace` instance of its own — `Mathlib`
deliberately keeps `EuclideanSpace`'s norm/inner-product structure on the `WithLp`-wrapped type
synonym, not the bare Pi type, to avoid instance diamonds) and wires it into `Spine.coerc_u_main`
(§5b of `COERCIVITY_STATEMENT_REPAIR.md`'s own required change, applied here, in `Spine.lean`).

**What this closes and what it does NOT** (per the dispatch's own explicit prediction, confirmed
here, not merely anticipated): `anchoredV` below is the FIXED, source-derived value `V` must equal
in the new `coerc_u_main` — no longer a free field a term can set to anything. `Δ` remains free.
`positiveLineAnchored_survives` below is the honest, disclosed demonstration that this is not enough
on its own: a scaled orthogonal projector built directly from `anchoredV` (not from `Δ_k(U)`, which
still does not exist in this tree) satisfies EVERY requirement the new anchored statement states,
`cohyp.V = anchoredV y x` included, by construction. Anchoring `V` alone narrows the attack surface
(the witness must now be built ON the real Balaban lattice type, referencing `Γ_{y,x}` concretely)
but does not close the family — exactly as `RGLinearization.lean`'s sibling lane (out of this
dispatch's scope, NO-GO) building `Δ_k(U)` is needed to finish. -/

namespace Anchoring

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace

variable {Lat : PeriodicLatticeExtent}

/-- **The anchored Hilbert space.** `AdmissibleSubspace.Bond Lat → ℝ` (the bare Pi type
`admissibleSubspace` is stated on) promoted to `EuclideanSpace`'s `WithLp`-wrapped carrier, so it
genuinely carries `[NormedAddCommGroup]`/`[InnerProductSpace ℝ]` (`Bond Lat` is a `Fintype`
automatically — a finite product of `Fin`-indexed `Fintype`s — so this is finite-dimensional with
no extra hypothesis). -/
noncomputable abbrev AnchoredBondSpace (Lat : PeriodicLatticeExtent) : Type :=
  EuclideanSpace ℝ (Bond Lat)

/-- **`(2.121)`'s admissible subspace, transported to the anchored Hilbert space.** `Submodule.map`
along `WithLp.linearEquiv`'s inverse — a genuine linear ISOMORPHISM between the bare Pi type
`admissibleSubspace` lives on and `AnchoredBondSpace Lat`'s underlying carrier, so this is the SAME
subspace, re-typed, not a reconstruction that could silently drift from `Γ_{y,x}`'s bond set.

**R2 CONSUMER PATCH (2026-07-21, `CONSUMER_PATCH_R2.md`)**: `admissibleSubspace` gained the
`(2.121)` antecedents `ell`/`hy : y ∈ CoarseLattice Lat ell`/`hx : x ∈ blockOf y ell` as required
explicit parameters (`Balaban/AdmissibleSubspace.lean` R2). Threaded straight through here —
mechanical, no new mathematics: the transported subspace is the SAME set, now honestly requiring
the geometry it claims to be conditioned on. -/
noncomputable def anchoredV (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) :
    Submodule ℝ (AnchoredBondSpace Lat) :=
  Submodule.map (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).symm.toLinearMap
    (admissibleSubspace y x ell hy hx)

/-! ## §6a — THE INTERSECTION, transported (V-scope repair, this pass)

`anchoredV` above transports ONE pair's `admissibleSubspace y x ell hy hx`. CMP96 `(2.121)`'s own
sentence is universal in BOTH `y ∈ Λ'` and `x ∈ B(y)` (`AdmissibleSubspace.lean` §4b's docstring,
re-derived from the same rendered page); `anchoredVInter` below transports the corresponding
INTERSECTION object, `admissibleSubspaceInter`, by the identical `Submodule.map` construction —
mechanical, no new mathematics, the SAME linear isomorphism `anchoredV` already uses. -/

/-- **`(2.121)`'s admissible subspace, literally — transported to the anchored Hilbert space.**
The intersection object (`AdmissibleSubspace.admissibleSubspaceInter`, universal over every valid
`(y,x)` pair), re-typed along the same `WithLp` linear equivalence `anchoredV` uses. This is the
`V` `coerc_u_main` (`Spine.lean`) now pins `cohyp.V` to, replacing the single-pair `anchoredV`. -/
noncomputable def anchoredVInter (ell : ℕ) : Submodule ℝ (AnchoredBondSpace Lat) :=
  Submodule.map (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).symm.toLinearMap
    (admissibleSubspaceInter Lat ell)

/-- **Faithfulness, transported**: `anchoredVInter` is genuinely CONTAINED IN every individual
pair's `anchoredV` — the anchored-space image of `AdmissibleSubspace.admissibleSubspaceInter_le`,
carried across the same linear equivalence (`Submodule.map` is monotone,
`Submodule.map_mono`). Confirms the transport preserves the intersection's defining property, not
merely its shape. -/
theorem anchoredVInter_le {y x : PeriodicLatticeSite Lat} {ell : ℕ}
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) :
    anchoredVInter ell ≤ anchoredV y x ell hy hx := by
  unfold anchoredVInter anchoredV
  exact Submodule.map_mono (admissibleSubspaceInter_le hy hx)

/-- **`anchoredVInter ell ≠ ⊥`, UNCONDITIONALLY — every `Lat`, every `ell`, no extra hypothesis
(grade-2 gate repair, this pass, closing item 1 of the four QUALIFIED findings).** Transports
`AdmissibleSubspace.admissibleSubspaceInter_ne_bot` (§4c of that file) across the SAME `WithLp`
linear equivalence `anchoredVInter`/`anchoredV` already use, via `Submodule.map_ne_bot_iff` (a
linear equivalence induces an order isomorphism of submodules, so it preserves `≠ ⊥` exactly —
`Submodule.orderIsoMapComap`, no approximation). This is the object `Spine.coerc_u_main` pins
`cohyp.V` to; `CoercivityHypothesis.V_ne_bot` is a mandatory field of every instance, so this
theorem is what makes that field genuinely discharge-able against the faithful `(2.121)` target,
not merely the strict-subset fact `AdmissibleSubspace.admissibleSubspaceInter_strict_witness`
carried. -/
theorem anchoredVInter_ne_bot (ell : ℕ) : anchoredVInter (Lat := Lat) ell ≠ ⊥ := by
  unfold anchoredVInter
  rw [Submodule.map_ne_bot_iff]
  exact admissibleSubspaceInter_ne_bot Lat ell

#print axioms anchoredVInter
#print axioms anchoredVInter_le
#print axioms anchoredVInter_ne_bot

/-- **Non-degeneracy, transported.** `Submodule.map_ne_bot_iff` (a linear EQUIVALENCE induces an
order isomorphism of submodules, Mathlib `Submodule.orderIsoMapComap`) carries `admissibleSubspace_
ne_bot_of_exists` across the equiv with no new mathematics — the transport is exact, not an
approximation. -/
theorem anchoredV_ne_bot {y x : PeriodicLatticeSite Lat} {ell : ℕ}
    {hy : y ∈ CoarseLattice Lat ell} {hx : x ∈ blockOf y ell} (b₀ : Bond Lat)
    (hb₀ : b₀ ∉ staircasePath y x) : anchoredV y x ell hy hx ≠ ⊥ := by
  unfold anchoredV
  rw [Submodule.map_ne_bot_iff]
  exact admissibleSubspace_ne_bot_of_exists b₀ hb₀

/-- **Properness, transported**, the same way. Not consumed by `CoercivityHypothesis` (which only
requires `V ≠ ⊥`), but recorded so the anchoring is confirmed genuinely restrictive on the anchored
side too, not merely on the pre-transport side. -/
theorem anchoredV_ne_top {y x : PeriodicLatticeSite Lat} {ell : ℕ}
    {hy : y ∈ CoarseLattice Lat ell} {hx : x ∈ blockOf y ell}
    (hne : (staircasePath y x).Nonempty) :
    anchoredV y x ell hy hx ≠ ⊤ := by
  unfold anchoredV
  rw [Submodule.map_ne_top_iff]
  exact admissibleSubspace_ne_top_of_nonempty hne

/-- **Concrete, fully closed non-degeneracy** on `AdmissibleSubspace`'s own witness lattice
(LAW-19: reusing `witnessY`/`witnessX`/`witnessOutsideBond`/`witnessOutsideBond_not_mem`, not
re-deriving a second witness). -/
theorem anchoredV_witness_ne_bot :
    anchoredV (Lat := witnessL) witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block
      ≠ ⊥ :=
  anchoredV_ne_bot witnessOutsideBond witnessOutsideBond_not_mem

theorem anchoredV_witness_ne_top :
    anchoredV (Lat := witnessL) witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block
      ≠ ⊤ :=
  anchoredV_ne_top witness_staircasePath_nonempty

/-- **A reusable general fact**: a scaled orthogonal projector onto ANY submodule distinguishes any
two distinct scale factors, on any nonzero vector of the submodule. Generalizes `cheapWitness_
nonconstant`'s argument away from the specific `CheapWitnessV`/`EuclideanSpace.single` choice, so it
applies verbatim to `anchoredV` (a submodule this file does not get to pick the shape of). -/
theorem scaledProjector_nonconstant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Submodule ℝ H) [S.HasOrthogonalProjection] {w : H} (hw : w ∈ S) (hwne : w ≠ 0)
    (c₁ c₂ : ℝ) (hne : c₁ ≠ c₂) :
    (c₁ • S.starProjection) w ≠ (c₂ • S.starProjection) w := by
  have hPw : S.starProjection w = w := Submodule.starProjection_eq_self_iff.mpr hw
  simp only [smul_apply, hPw]
  intro hcontra
  have hsub : (c₁ - c₂) • w = 0 := by rw [sub_smul, hcontra, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact hne (sub_eq_zero.mp h)
  · exact hwne h

/-- **`Δ` on the anchored space, still a free scaled-projector family** — `Δ_k(U)` itself does not
exist in this tree (`RGLinearization.lean` is a SIBLING lane's deliverable, NO-GO here); this is the
honest report of what remains choosable even after `V` stops being. **R2 consumer patch**: `ell hy
hx` threaded through to `anchoredV` (mechanical). -/
noncomputable def anchoredΔ (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) (c₁ c₂ : ℝ) :
    ℕ → Bool → AnchoredBondSpace Lat →L[ℝ] AnchoredBondSpace Lat :=
  fun _ U => (cond U c₁ c₂) • (anchoredV y x ell hy hx).starProjection

theorem anchoredΔ_coercive (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) (c₁ c₂ : ℝ) (_h1 : 0 < c₁)
    (_h2 : 0 < c₂) :
    ∀ (k : ℕ) (U : Bool), ∀ v ∈ anchoredV y x ell hy hx,
      (min c₁ c₂) * ‖v‖ ^ 2 ≤ inner ℝ v (anchoredΔ y x ell hy hx c₁ c₂ k U v) := by
  intro k U v hv
  have hPv : (anchoredV y x ell hy hx).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  have hnn : (0:ℝ) ≤ ‖v‖ ^ 2 := by positivity
  cases U with
  | true =>
    simp only [anchoredΔ, cond_true, smul_apply, hPv]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hnn
  | false =>
    simp only [anchoredΔ, cond_false, smul_apply, hPv]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hnn

theorem anchoredΔ_nonconstant (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) (b₀ : Bond Lat)
    (hb₀ : b₀ ∉ staircasePath y x) (c₁ c₂ : ℝ) (hne : c₁ ≠ c₂) :
    anchoredΔ y x ell hy hx c₁ c₂ 0 true ≠ anchoredΔ y x ell hy hx c₁ c₂ 0 false := by
  obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (anchoredV_ne_bot (ell := ell) (hy := hy) (hx := hx) b₀ hb₀)
  intro hcontra
  have heval := DFunLike.congr_fun hcontra w
  simp only [anchoredΔ, cond_true, cond_false] at heval
  exact scaledProjector_nonconstant (anchoredV y x ell hy hx) hw hwne c₁ c₂ hne heval

/-- **The honest finding, kernel-checked**: `V` anchored to the REAL `(2.121)` subspace does NOT by
itself close `[LEM-COERC-U]`'s S91 attack family. A full `CoercivityHypothesis (AnchoredBondSpace
Lat) Bool` term, with `V` FORCED to equal `anchoredV y x ell hy hx` (not a free choice), built from
nothing but a scaled projector onto it. This is the disclosed, predicted-and-confirmed residual:
anchoring `V` narrows the required forgery (it must reference the real lattice type and `Γ_{y,x}`
concretely) but `Δ` staying free is enough to keep the family alive. **R2 consumer patch**: `ell hy
hx` inserted immediately after `x`, before `b₀`, matching `anchoredV`'s new required antecedents. -/
noncomputable def positiveLineAnchored_survives (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    (b₀ : Bond Lat) (hb₀ : b₀ ∉ staircasePath y x) (c₁ c₂ : ℝ) (h1 : 0 < c₁) (h2 : 0 < c₂)
    (hne : c₁ ≠ c₂) : CoercivityHypothesis (AnchoredBondSpace Lat) Bool where
  Δ := anchoredΔ y x ell hy hx c₁ c₂
  V := anchoredV y x ell hy hx
  V_ne_bot := anchoredV_ne_bot b₀ hb₀
  Δ_nonconstant :=
    ⟨0, true, false, by decide, anchoredΔ_nonconstant y x ell hy hx b₀ hb₀ c₁ c₂ hne⟩
  γ'' := min c₁ c₂
  γ''_pos := lt_min h1 h2
  coercive := anchoredΔ_coercive y x ell hy hx c₁ c₂ h1 h2

/-- **`V` really is forced to the anchored value, by construction** — the exact conjunct
`Spine.coerc_u_main`'s new statement demands, confirming this witness genuinely satisfies it
(rather than merely being of the right STRUCTURE type). -/
theorem positiveLineAnchored_survives_V_eq (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    (b₀ : Bond Lat) (hb₀ : b₀ ∉ staircasePath y x) (c₁ c₂ : ℝ) (h1 : 0 < c₁) (h2 : 0 < c₂)
    (hne : c₁ ≠ c₂) :
    (positiveLineAnchored_survives y x ell hy hx b₀ hb₀ c₁ c₂ h1 h2 hne).V
      = anchoredV y x ell hy hx := rfl

/-- L7 — non-vacuity of the honest-residual instance itself, matching `positiveLine_generalized_
survives_nontrivial`'s pattern for the anchored case. -/
theorem positiveLineAnchored_survives_nontrivial (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    (b₀ : Bond Lat) (hb₀ : b₀ ∉ staircasePath y x) (c₁ c₂ : ℝ) (h1 : 0 < c₁) (h2 : 0 < c₂)
    (hne : c₁ ≠ c₂) :
    Nonempty (CoercivityHypothesis (AnchoredBondSpace Lat) Bool)
      ∧ (positiveLineAnchored_survives y x ell hy hx b₀ hb₀ c₁ c₂ h1 h2 hne).V ≠ ⊥
      ∧ 0 < (positiveLineAnchored_survives y x ell hy hx b₀ hb₀ c₁ c₂ h1 h2 hne).γ'' :=
  ⟨⟨positiveLineAnchored_survives y x ell hy hx b₀ hb₀ c₁ c₂ h1 h2 hne⟩,
    anchoredV_ne_bot b₀ hb₀, lt_min h1 h2⟩

end Anchoring

end AdalyFormal.Balaban

#print axioms AdalyFormal.Balaban.CoercivityHypothesis.coercive_of_top
#print axioms AdalyFormal.Balaban.CoercivityHypothesis.ofUnrestricted
#print axioms AdalyFormal.Balaban.CoercivityHypothesis.ofUnrestricted_V
#print axioms AdalyFormal.Balaban.CoercivityHypothesis.ofUnrestricted_data_roundtrip
#print axioms AdalyFormal.Balaban.CoercivityHypothesis.composes_with_L8c
#print axioms AdalyFormal.Balaban.CoercivityHypothesis.V_ne_bot_always
#print axioms AdalyFormal.Balaban.botZero_no_longer_inhabits
#print axioms AdalyFormal.Balaban.punit_not_nontrivial
#print axioms AdalyFormal.Balaban.cheapWitnessV_ne_bot
#print axioms AdalyFormal.Balaban.cheapWitness_coercive
#print axioms AdalyFormal.Balaban.cheapWitness_nonconstant
#print axioms AdalyFormal.Balaban.positiveLine_generalized_survives_nontrivial
#print axioms AdalyFormal.Balaban.Anchoring.anchoredV_ne_bot
#print axioms AdalyFormal.Balaban.Anchoring.anchoredV_ne_top
#print axioms AdalyFormal.Balaban.Anchoring.anchoredV_witness_ne_bot
#print axioms AdalyFormal.Balaban.Anchoring.anchoredV_witness_ne_top
#print axioms AdalyFormal.Balaban.Anchoring.anchoredVInter
#print axioms AdalyFormal.Balaban.Anchoring.anchoredVInter_le
#print axioms AdalyFormal.Balaban.Anchoring.anchoredVInter_ne_bot
#print axioms AdalyFormal.Balaban.Anchoring.scaledProjector_nonconstant
#print axioms AdalyFormal.Balaban.Anchoring.anchoredΔ_coercive
#print axioms AdalyFormal.Balaban.Anchoring.anchoredΔ_nonconstant
#print axioms AdalyFormal.Balaban.Anchoring.positiveLineAnchored_survives_V_eq
#print axioms AdalyFormal.Balaban.Anchoring.positiveLineAnchored_survives_nontrivial
