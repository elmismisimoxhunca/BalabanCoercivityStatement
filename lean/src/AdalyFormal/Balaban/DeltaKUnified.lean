/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKAssemblyRepaired
import AdalyFormal.Balaban.Q1Real

set_option autoImplicit false

/-!
# `DeltaKUnified` — the `Δ_k` form AND the `(3.156)` subspace on ONE real Lean carrier

## ⚠⚠ CORRECTION BANNER — `Q := 1` MEANS THERE IS NO SCHUR COMPLEMENT HERE (added 2026-07-26)

Filed by the level-collapse sweep as finding **F4**
(`compute/level_collapse_sweep/FINDINGS.md` §1). **Read this before consuming anything below.**

`deltaKUnifiedData` (§5b) sets `Q := 1`, `Qstar := 1`, and `Comp := GstarBFL2`; and `GstarBFL2` is
proved to be the SCALAR `2 • 1` (`wG1BFL2_eq`, used in `GinvBFL2_GstarBFL2`), so
`CompInv = GinvBFL2 = (1/2) • 1`. `DeltaKAssembly.deltaKForm`'s leading term is
`⟨B, (Q G₁ Q*)⁻¹ B⟩` (`BalabanCovarianceData.CompInv`, whose docstring names it exactly that).
Here that term is therefore

    ⟨B, (Q G₁ Q*)⁻¹ B⟩  =  ⟨B, (1/2) • B⟩  =  (1/2)‖B‖².

**Consequences, stated plainly:**

1. **There is no Schur complement in this object.** `(Q G₁ Q*)⁻¹` is the whole of CMP99b
   (3.156)'s fibre integration over the fine level; with `Q = Q* = 1` the fine and unit levels
   are the same space and nothing is integrated out. With `G₁` additionally scalar, the leading
   term carries no operator content at all.
2. **This object is not `Δ_k` in any sense**, and no statement proved about it transfers to
   Bałaban's `Δ_k` merely by being proved here. The title line of this file ("the `Δ_k` form")
   is ASPIRATIONAL — it names the SHAPE (`DeltaKAssembly.deltaKForm`'s three summands) that is
   instantiated, not a faithful instance.
3. `CarrierBridge.carrierBridgeFamily` does the same with `Q₁ := 0`, and `DeltaKAssembly`'s own
   toy (`EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1)`) keeps `H ≠ K` — so the toy is
   **more faithful on this axis** than the object built to supersede it.
4. The tree ALREADY convicted this collapse downstream, twice and de-correlated
   (`compute/prosecute_su2_build/VERDICT.md`, `compute/sol_su2_gate/SOL_VERDICT.md`, both quoted in
   `FaithfulDeltaKNonScalar.lean`'s header: `deltaKC_su2(U) v = s(U) • …` for EVERY `v`, EVERY
   `U`, "`Q := Qstar := 1` and `H₁ := id` (both inherited from `DeltaKUnified.lean`)"). Those
   verdicts were recorded at the CONSUMER, never here at the definition. This banner closes
   that gap.

### WHAT REMAINS TRUE — the exact list

* **Every theorem in this file and its consumers is a TRUE theorem about `deltaKUnifiedData`.**
  Nothing below is being retracted; no `#print axioms` line changes. What is corrected is the
  DENOTATION, not the mathematics.
* §1's carrier work (`BFL2`, its `NormedAddCommGroup`/`InnerProductSpace`/`FiniteDimensional`/
  `CompleteSpace` instances, the §0 diamond measurement) is genuine and independent of `Q`.
* §3's `subspace156BFL2 ≠ ⊥`, and
  `Subspace156NonDegenerate.subspace156BFL2_nondegenerate_ne_bot`,
  are statements about the **subspace only**. They never mention the form, and the subspace IS built
  from the real `Q1Real.q1RealKernel U`. They are unaffected by `Q := 1` and remain faithful on
  their own axis. (Their reading must not be upgraded to "the domain of `Δ_k` is non-vacuous"
  *together with* a form that is not `Δ_k` — that composite is the F4 hazard.)
* §4's well-typedness deliverable (`deltaKFormOnSubspace156` is ONE well-typed object on ONE
  carrier) is genuine: it is a TYPE-LEVEL result, and it holds for any `BalabanCovarianceData` on
  `BFL2 witnessL`, faithful or not.

### WHAT DOES **NOT** TRANSFER — named consumers

Each of these is a true theorem, and each is FORCED by `Q = Qstar = 1` plus `Gstar = 2•1`; none is
evidence about `Δ_k`:

* `RegularUCoercivity.deltaKFormOnSubspace156_U_independent` and
  `…_trivialU_eq_any` — "the form's value contains no occurrence of `U`". In (3.156) BOTH
  `Q = Q(U)` and `G₁ = G₁(U)` depend on the background; here both have been replaced by `U`-free
  constants, so the `U`-independence is an artifact of `Q := 1`, not a property of `Δ_k`. In
  particular the conclusion drawn from it — that "the CMP122-II perturbation-decomposition
  skeleton is VACUOUS" — is a fact about THIS artifact only, and must not be read as evidence
  that `Δ_k` has no perturbation term.
* `RegularUCoercivity.deltaKUnifiedData_first_two_terms_eq` / `…_coercive`
  (`⟨B,CompInv B⟩ − a⟨B,B⟩ = (1/2 − a)‖B‖²`). The `1/2` IS `GinvBFL2`'s scalar. This is
  the coercivity of `(1/2 − a)·id`, not of `(Q G₁ Q*)⁻¹ − a`.
* `RegularUCoercivity.theLemma_regularU_false_without_source_constraint` and
  `CoercivityAdaptation`'s generalizations of it. As REFUTATIONS these are sound — they refute
  `TheLemmaRegularU`, a `Prop` defined in terms of `deltaKFormOnSubspace156` itself, at a legal
  instance. What does NOT follow is the accompanying DIAGNOSIS ("the missing primitive is a
  constraining hypothesis on `Qext`/`J`"): that diagnosis was read off an object whose first two
  terms are a scalar, and the real `(Q G₁ Q*)⁻¹` could change which term dominates.
* `RegularUCoercivity.deltaKFormOnSubspace156_strictAntitone_in_a` — true, and it does establish
  `deltaKForm ≠ deltaKQuadFormCorrected` structurally (that argument only needs the free `a`), so
  it survives; but it says nothing about faithfulness to (3.156).
* `FaithfulCoercivitySU2` / `FaithfulDeltaKNonScalar` / `UDependentForm` / `BoundedReparam` — all
  already carry their own disclosures of this exact collapse; `FaithfulDeltaKNonScalar` exists
  BECAUSE of it.

**No consumer's Lean statement is falsified by `Q := 1`.** The defect is denotational, and the
repair is this banner. Nothing is silently redefined here; a faithful `Q` needs a second, smaller
real carrier and a real block-averaging map, which §5 item 2 already names as open.

---

**Dispatch target**: break the recurring `PILP_BRIDGE` carrier wall named in
`DeltaKAssemblyRepaired.lean` §6b — `deltaKForm` computed on a TOY `EuclideanSpace ℝ (Fin 1)`
witness, `subspace156` living on the REAL `Bond L → ℝ`/`Bond L → SuTwo` fine-bond space — by putting
BOTH on ONE carrier, so "`deltaKForm` restricted to `subspace156`" becomes a single well-typed
statement. **Coercivity is NOT claimed anywhere in this file** (per the dispatch).

**Does not edit** `DeltaKAssemblyRepaired.lean`, `Q1Real.lean`, `DomainSequence.lean`,
`AxialContour.lean`, `CovarianceG1.lean`, `VariationalProjectorH1.lean`, `ConstantA.lean`,
`SourceJ.lean`, or `DeltaKFull.lean` — every ingredient is IMPORTED and REUSED (LAW-19).

## HEADLINE, stated first per the dispatch's own lead requirement

1. **`deltaKFormOnSubspace156` IS one well-typed object** (§4): the real `deltaKForm`, restricted to
   the real `subspace156`, both on the carrier `BFL2 witnessL`. It compiles with `#print axioms`
   clean (`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`).
2. **`subspace156BFL2 ≠ ⊥` IS PROVED** (§3), by an explicit joint nonzero witness
   (`Q1Real.checkerConfigSuTwo`) satisfying all three (3.156) clauses SIMULTANEOUSLY — at a
   specific, disclosed, non-generic parameter choice (`Lambda := Finset.univ`, `S' := ∅`,
   `U := trivialU`). This is a genuine advance: the prior file left `≠ ⊥` entirely open.
3. **The carrier promotion DID hit two real instance obstructions**, both closed here, neither
   papered over (§1's own §1a/§1b): (a) `BondFnL2 L`'s own AMBIENT registered instance
   (`CovariantOperators.instNormedAddCommGroupBondFnL2`, `Matrix.Norms.L2Operator`-scoped) collides
   with the `PiLp`-generic instance Mathlib derives automatically from `SuTwo`'s own canonical
   `InnerProductSpace ℝ SuTwo` — REPRODUCED DIRECTLY as `sorryAx` insertion + a hard
   `synthInstanceFailed` error the moment a `BalabaCovarianceData`-shaped structure needs BOTH
   `[NormedAddCommGroup H]` and `[InnerProductSpace ℝ H]` as sibling instance arguments at
   `H := CovariantOperators.BondFnL2 witnessL` (this is the SAME `PILP_BRIDGE`/`CoercivityCov.lean`
   diamond, here shown to be intrinsic to `CovariantOperators.BondFnL2` itself the moment `SuTwoInner`
   is transitively imported — NOT specific to importing `CoercivityCov`/`HarmonicModes` together, as
   `CarrierBridge.lean` had characterized it); (b) `CompleteSpace` does not synthesize automatically
   for a freshly-defined carrier type even after the `NormedAddCommGroup`/`InnerProductSpace` pair is
   forced — needs an explicit `FiniteDimensional` instance first. Both fixed by declaring a genuinely
   FRESH, non-`abbrev` carrier `BFL2` with EXPLICIT, internally-consistent `PiLp.normedAddCommGroup`/
   `PiLp.innerProductSpace`/`FiniteDimensional`/`CompleteSpace` instances (§1), never touching
   `CovariantOperators.BondFnL2`'s own registered instance.

## §0 — THE WALL, measured directly, not assumed (reproduced from this dispatch's own scratch work)

Plain `inferInstance` for `NormedAddCommGroup (CovariantOperators.BondFnL2 witnessL)` and
`InnerProductSpace ℝ (CovariantOperators.BondFnL2 witnessL)` EACH individually succeed (`#synth`
reports `AdalyFormal.Balaban.CovariantOperators.instNormedAddCommGroupBondFnL2` for the first,
`PiLp.innerProductSpace fun x => ↥SuTwo` for the second) — exactly `BondSU2Space.lean`'s own §0 two
individually-true checks. But the moment a consumer needs BOTH as sibling instance arguments of one
structure (`VariationalProjectorH1.BalabanCovarianceData H K` demands
`[NormedAddCommGroup H] [InnerProductSpace ℝ H]` separately), elaboration of a concrete instance of
that structure at `H := CovariantOperators.BondFnL2 witnessL` FAILS with
`synthInstanceFailed : InnerProductSpace ℝ (BondFnL2 witnessL)` inside field bodies that need
`real_inner_self_nonneg`-shaped facts, and Lean's error-recovery silently inserts `sorryAx` rather
than a hard stop — caught only by requiring `#print axioms` to be clean, exactly the discipline this
file's own gate follows. This is `CoercivityCov.lean`'s exact diamond, ONE FILE EARLIER than where
`CarrierBridge.lean` first met it (that file needed BOTH the `DeltaKFull` chain AND the
`HarmonicModes` chain imported together to trigger it; here it is intrinsic to `CovariantOperators
.BondFnL2` itself the instant `SuTwoInner` — needed for `Q1Real`'s own `RMap`/`SuTwo` machinery — is
transitively in scope, which it unavoidably is for this dispatch since `Q1Real.lean` is a REQUIRED
ingredient).
-/

namespace AdalyFormal.Balaban.DeltaKUnified

open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond witnessY witnessEll)
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)

/-! ## §1 — `BFL2`, the ONE carrier: a FRESH type (not `CovariantOperators.BondFnL2`), with an
EXPLICIT, internally-consistent instance pair, sidestepping §0's diamond by construction rather than
by reconciliation (`PILP_BRIDGE.md`'s own prescribed fix, applied one level over: prove/construct on
an abstract carrier with NO competing ambient instance, rather than trying to unify two already-
registered ones after the fact). -/

/-- **THE carrier.** `WithLp 2 (Bond L → SuTwo)` — literally `PiLp 2 (fun _ => SuTwo)`'s underlying
shape, but declared as a fresh, non-`abbrev` `def` so anonymous instance search never reaches for
`CovariantOperators.instNormedAddCommGroupBondFnL2` (registered on the DIFFERENT head symbol
`CovariantOperators.BondFnL2`) when resolving instances for THIS type. -/
def BFL2 (Lat : PeriodicLatticeExtent) : Type := WithLp 2 (Bond Lat → SuTwo)

/-- §1a — the forced, internally-consistent `NormedAddCommGroup`/`InnerProductSpace` pair, BOTH
built from the SAME `PiLp.normedAddCommGroup`/`PiLp.innerProductSpace` family (mirroring
`CoercivityCov.lean`'s own established recipe for `instNormedAddCommGroupBondFnL2Cov`/
`instInnerProductSpaceBondFnL2Cov`, applied to a FRESH type instead of reusing `BondFnL2`). -/
noncomputable instance instNormedAddCommGroupBFL2 {Lat : PeriodicLatticeExtent} :
    NormedAddCommGroup (BFL2 Lat) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : Bond Lat => SuTwo)

noncomputable instance instInnerProductSpaceBFL2 {Lat : PeriodicLatticeExtent} :
    InnerProductSpace ℝ (BFL2 Lat) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (f := fun _ : Bond Lat => SuTwo)

/-- §1b — the SECOND obstruction, closed: `CompleteSpace (BFL2 Lat)` (needed by
`CovarianceG1.gOneOfNeumann`, §5) does NOT synthesize from `instNormedAddCommGroupBFL2`/
`instInnerProductSpaceBFL2` alone (measured directly: `#synth CompleteSpace (BFL2 witnessL)` fails
without the two instances below) — a finite-dimensional real inner-product space is complete, but
Lean needs the `FiniteDimensional` fact made explicit first, again because `BFL2` is a fresh,
non-reducible type that ambient search will not unfold on its own. -/
noncomputable instance instFiniteDimensionalBFL2 {Lat : PeriodicLatticeExtent} :
    FiniteDimensional ℝ (BFL2 Lat) :=
  (inferInstance : FiniteDimensional ℝ (PiLp 2 (fun _ : Bond Lat => SuTwo)))

noncomputable instance instCompleteSpaceBFL2 {Lat : PeriodicLatticeExtent} :
    CompleteSpace (BFL2 Lat) :=
  FiniteDimensional.complete ℝ (BFL2 Lat)

/-- The genuine `LinearEquiv` between `BFL2 Lat` and the bare function type `Bond Lat → SuTwo` —
literally `WithLp.linearEquiv`, the SAME transport primitive `DeltaKAssemblyRepaired.lean`'s
`wQL2`/`wQL2Plus`/`wQL2_2` and `DeltaKFull.lean` §5's `curlCovariantLM_L2` already use for exactly
this "promote a bare-Pi-type construction onto the `WithLp`-wrapped carrier" move (LAW-19). No norm
claim is made or needed across it anywhere in this file (matching `CarrierBridge.lean`'s own
disclosure for the analogous `bondFnL2Equiv`: `Submodule` transport via `Submodule.map`/`comap` along
a `LinearEquiv` needs no norm-preservation fact, only linearity). -/
noncomputable def bfl2Equiv {Lat : PeriodicLatticeExtent} : BFL2 Lat ≃ₗ[ℝ] (Bond Lat → SuTwo) :=
  WithLp.linearEquiv 2 ℝ (Bond Lat → SuTwo)

#print axioms instNormedAddCommGroupBFL2
#print axioms instInnerProductSpaceBFL2
#print axioms instFiniteDimensionalBFL2
#print axioms instCompleteSpaceBFL2
#print axioms bfl2Equiv

/-! ## §2 — THE `(3.156)` SUBSPACE, `SuTwo`-valued, on the bare function type, then transported

`DeltaKAssemblyRepaired.lean`'s own `LambdaComplementLocus`/`AxialContour.AxUnionLocus` are hardcoded
`Submodule ℝ (Bond L → ℝ)` — REAL-valued fine bond fields, not `SuTwo`-valued ones, so they cannot be
directly reused at `BFL2`'s codomain (there is no natural map between `ℝ`-valued and `SuTwo`-valued
bond fields to bridge them). This section builds the `SuTwo`-valued ANALOGS, REUSING the underlying
GEOMETRY (`AxialContour.Ax`, the bond SET, which is codomain-independent) rather than rebuilding it —
only the field's codomain changes, exactly the generalization the dispatch's item 3 anticipates
("use `Q1Real.lean`'s real kernel ... which now MATCHES the carrier"). `Q1Real.lean`'s own
`q1RealKernel` is ALREADY `Submodule ℝ (Bond witnessL → SuTwo)` — reused verbatim, not rebuilt. -/

/-- **Clause 1, `SuTwo`-valued: `B = 0` on `Λᶜ`.** Same shape as `DeltaKAssemblyRepaired
.LambdaComplementLocus`, at the `SuTwo` codomain `Q1Real`'s objects actually live in. -/
def LambdaComplementLocusG {Lat : PeriodicLatticeExtent}
    (Lambda : Finset (PeriodicLatticeSite Lat)) : Submodule ℝ (Bond Lat → SuTwo) where
  carrier := {B | ∀ b : Bond Lat, b.1 ∉ Lambda → B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by intro B1 B2 hB1 hB2 b hb; simp [hB1 b hb, hB2 b hb]
  smul_mem' := by intro c B hB b hb; simp [hB b hb]

theorem mem_LambdaComplementLocusG {Lat : PeriodicLatticeExtent}
    {Lambda : Finset (PeriodicLatticeSite Lat)} {B : Bond Lat → SuTwo} :
    B ∈ LambdaComplementLocusG Lambda ↔ ∀ b : Bond Lat, b.1 ∉ Lambda → B b = 0 := Iff.rfl

open AdalyFormal.Balaban.AxialContour (Ax)

/-- **Clause 2, `SuTwo`-valued: `B = 0` on `⋃_{y∈S} Ax(y)`.** REUSES `AxialContour.Ax` (the bond
SET, imported not rebuilt) — only the FIELD's codomain (`SuTwo` instead of `ℝ`) is new, matching the
same shape as `AxialContour.AxUnionLocus`. -/
def AxUnionLocusG {L : PeriodicLatticeExtent} (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    Submodule ℝ (Bond L → SuTwo) where
  carrier := {B | ∀ y ∈ S, ∀ b ∈ Ax y ell, B b = 0}
  zero_mem' := by intro y _ b _; rfl
  add_mem' := by intro B1 B2 hB1 hB2 y hy b hb; simp [hB1 y hy b hb, hB2 y hy b hb]
  smul_mem' := by intro c B hB y hy b hb; simp [hB y hy b hb]

theorem mem_AxUnionLocusG {L : PeriodicLatticeExtent} {S : Finset (PeriodicLatticeSite L)}
    {ell : ℕ} {B : Bond L → SuTwo} :
    B ∈ AxUnionLocusG S ell ↔ ∀ y ∈ S, ∀ b ∈ Ax y ell, B b = 0 := Iff.rfl

open AdalyFormal.Balaban.Q1Real (q1RealKernel checkerConfigSuTwo checkerConfigSuTwo_ne_zero
  checkerConfigSuTwo_mem_q1RealKernel_trivialU)

/-- **`subspace156`, `SuTwo`-valued, assembled from all THREE real clauses**, `Q₁`'s clause now the
REAL, per-bond, path-dependent `Q1Real` kernel (not the abelian `qOnePathSumLM` the earlier file
used) — matching the dispatch's explicit instruction. Fixed at `Lat := witnessL` because `Q1Real`
itself is (`Q1Real.lean`'s own scope) only built at `witnessL`/`witnessEll`, not generic over an
arbitrary lattice — the SAME restriction `CarrierBridge.lean` §4's own docstring names for the
identical reason. -/
noncomputable def subspace156G (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Submodule ℝ (Bond witnessL → SuTwo) :=
  LambdaComplementLocusG Lambda ⊓ AxUnionLocusG S' ell ⊓ q1RealKernel U

/-- **`subspace156`, transported onto `BFL2 witnessL` via `Submodule.comap` along the genuine
`LinearEquiv` `bfl2Equiv`** — THE SAME "re-typing along an isomorphism" move `CoercivityCov.lean`'s
`anchoredVCov` (`Submodule.map` direction) already uses, here in the `comap` direction since we go
FROM the wrapped carrier's membership condition TO the bare-type one. No norm claim crosses this
map anywhere below. -/
noncomputable def subspace156BFL2 (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Submodule ℝ (BFL2 witnessL) :=
  Submodule.comap (bfl2Equiv (Lat := witnessL)).toLinearMap (subspace156G Lambda S' ell U)

#print axioms mem_LambdaComplementLocusG
#print axioms mem_AxUnionLocusG
#print axioms subspace156G
#print axioms subspace156BFL2

/-! ## §3 — `subspace156BFL2 ≠ ⊥`: THE SECOND NAMED RESIDUAL, CLOSED

**Disclosed precisely, not overclaimed**: proved at `Lambda := Finset.univ`, `S' := ∅`,
`U := trivialU witnessL`, `ell := witnessEll` — a specific, honestly-stated instantiation, not a
claim that `subspace156BFL2` is nonzero for EVERY choice of `Lambda`/`S'`/`U`. At this choice, clause
1 (`Λᶜ`) and clause 2 (`Ax`, `S' = ∅`) are BOTH forced trivial (`= ⊤`) by the parameter choice itself
— honestly stated below, not hidden — and the entire content of the non-vacuity proof is that the
THIRD clause, `q1RealKernel (trivialU witnessL)`, is ALREADY non-trivial (`Q1Real.lean`'s own
`checkerConfigSuTwo_mem_q1RealKernel_trivialU`/`checkerConfigSuTwo_ne_zero`, reused verbatim, LAW-19)
— so this file's genuine content is the CARRIER TRANSPORT (`Submodule.comap` along `bfl2Equiv`),
not a new non-vacuity argument for `q1RealKernel` itself. -/

/-- **Why `Lambda := Finset.univ` is FORCED, not merely convenient, for THIS witness**:
`checkerConfigSuTwo` (`Q1Real.lean` §9) is nonzero on EVERY site's direction-`0` bond
(`(-1)^(x 0).val • suTwoWitness`, never `0` since `suTwoWitness ≠ 0`), so clause 1 can only hold for
this specific witness if `Lambda` contains every site. A smaller, non-full `Lambda` genuinely
EXCLUDES this witness — checked directly below (S82 falsifiability), not merely asserted. -/
theorem checkerConfigSuTwo_notMem_LambdaComplementLocusG_empty :
    checkerConfigSuTwo ∉ LambdaComplementLocusG (∅ : Finset (PeriodicLatticeSite witnessL)) := by
  intro hmem
  rw [mem_LambdaComplementLocusG] at hmem
  have h0 := hmem (witnessY, (0 : Fin 3)) (Finset.notMem_empty witnessY)
  have hval : checkerConfigSuTwo (witnessY, (0 : Fin 3)) =
      AdalyFormal.Balaban.CovariantOperators.suTwoWitness := by
    simp [AdalyFormal.Balaban.Q1Real.checkerConfigSuTwo, witnessY,
      AdalyFormal.Balaban.AdmissibleSubspace.witnessY]
  rw [hval] at h0
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero h0

/-- **Falsifiability of clause 1, made concrete**: `subspace156BFL2` at `Lambda := ∅` is genuinely
`⊥` (a DIFFERENT, degenerate parameter choice, EXHIBITED, not merely claimed) — clause 1 alone forces
every bond to vanish when `Lambda` is empty, so the whole intersection collapses. This is the
mutation control confirming `Lambda := Finset.univ` is doing real work in the theorem below, not a
vacuous choice that would have worked at any `Lambda`. -/
theorem subspace156BFL2_eq_bot_of_lambda_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    subspace156BFL2 (∅ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U = ⊥ := by
  ext x
  simp only [Submodule.mem_bot]
  constructor
  · intro hmem
    apply (bfl2Equiv (Lat := witnessL)).injective
    rw [map_zero]
    funext b
    exact hmem.1.1 b (Finset.notMem_empty b.1)
  · intro hx
    subst hx
    exact Submodule.zero_mem _

#print axioms checkerConfigSuTwo_notMem_LambdaComplementLocusG_empty
#print axioms subspace156BFL2_eq_bot_of_lambda_empty

open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- **THE NAMED RESIDUAL, CLOSED: `subspace156BFL2 ≠ ⊥`.** An explicit joint nonzero witness
(`bfl2Equiv.symm checkerConfigSuTwo`) satisfying ALL THREE `(3.156)` clauses SIMULTANEOUSLY, at
`Lambda := Finset.univ`, `S' := ∅`, `U := trivialU witnessL`. -/
theorem subspace156BFL2_ne_bot :
    subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ witnessEll
        (trivialU witnessL) ≠ ⊥ := by
  intro hbot
  apply checkerConfigSuTwo_ne_zero
  have hmem : (bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo ∈
      subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ witnessEll
        (trivialU witnessL) := by
    show checkerConfigSuTwo ∈ subspace156G Finset.univ ∅ witnessEll (trivialU witnessL)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro b hb; exact absurd (Finset.mem_univ b.1) hb
    · intro y hy; exact absurd hy (Finset.notMem_empty y)
    · exact checkerConfigSuTwo_mem_q1RealKernel_trivialU
  rw [hbot, Submodule.mem_bot] at hmem
  have hc := congrArg (bfl2Equiv (Lat := witnessL)) hmem
  simpa using hc

#print axioms subspace156BFL2_ne_bot

/-! **Named, not attempted here**: whether a joint witness EXISTS at a genuinely non-trivial `S'`
(`S' ≠ ∅`) or a proper (`≠ univ`) `Lambda` remains open — `Q1Real.lean`'s own
`checkerConfigSuTwo_mem_q1RealKernel_trivialU` is itself already flagged there as "PROVED ONLY AT
`trivialU`" (the pointwise cancellation does not transfer term-by-term at a non-flat background), and
no witness with LOCALIZED (non-full-lattice) support has been constructed for `q1RealKernel` in this
tree. Left open, not forced. -/

/-! ## §4 — THE DELIVERABLE: `deltaKForm` restricted to `subspace156`, ONE well-typed object

`H := K := BFL2 witnessL` — a DISCLOSED simplification (Fine = Coarse collapsed onto the ONE
carrier), matching the dispatch's own instruction ("form, ingredients, subspace — lives here") and
the SAME kind of simplification `DeltaKRecursive.RGScaleFamily` already carried historically, now on
a REAL big carrier instead of a `1`-dimensional toy `H`. This is LESS faithful than
`DeltaKAssembly.lean`'s own toy witness on the specific axis of Fine≠Coarse (that file used genuinely
separate `EuclideanSpace ℝ (Fin 2)`/`(Fin 1)` spaces with a non-injective `Q`) — stated plainly, not
hidden, since resolving the CARRIER wall (this dispatch's actual target) and preserving Fine≠Coarse
simultaneously would need a genuine, real block-averaging `Q : BFL2 witnessL →L[ℝ] (smaller real
carrier)`, not attempted here. -/

open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.CovarianceG1 (gOneOfNeumann)

/-- `G₀ := 1`. -/
noncomputable def wG0BFL2 : BFL2 witnessL →L[ℝ] BFL2 witnessL := 1

/-- `P := (1/2)•1` — a genuine (non-zero, non-identity-collapsing) scalar perturbation, chosen so
`G₁ := gOneOfNeumann wG0BFL2 wPBFL2` is NOT the identity (§5a below computes it exactly as `2•1`,
confirmed by the SAME `Ring.inverse`-of-a-unit technique `DeltaKAssembly.lean`'s own `wG1_eq`/
`ring_inverse_diagCLM` uses, adapted to a scalar rather than a `2×2` diagonal since `BFL2 witnessL`
has no convenient coordinate basis to write a non-scalar diagonal operator against). -/
noncomputable def wPBFL2 : BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)

/-- §5a — **`G₁ = gOneOfNeumann wG0BFL2 wPBFL2 = 2•1`, computed, literally
`CovarianceG1.gOneOfNeumann`'s output on THIS carrier** — genuinely non-identity (`2 ≠ 1`), so this
is not a degenerate/trivial covariance. -/
theorem wG1BFL2_eq :
    gOneOfNeumann wG0BFL2 wPBFL2 = (2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) := by
  unfold gOneOfNeumann wG0BFL2 wPBFL2
  have h1 : (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) * 1 =
      (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) := by rw [mul_one]
  rw [h1]
  have h2 : (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) -
      (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)
      = (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) := by
    rw [← one_smul ℝ (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL), smul_smul]; module
  rw [h2]
  have hunit : (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) *
      (2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) = 1 := by
    rw [smul_mul_smul_comm, mul_one]; norm_num
  have hunit2 : (2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) *
      (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) = 1 := by
    rw [smul_mul_smul_comm, mul_one]; norm_num
  rw [one_mul]
  have hu := Ring.inverse_unit (Units.mk ((1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL))
    ((2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)) hunit hunit2)
  simpa using hu

#print axioms wG0BFL2
#print axioms wPBFL2
#print axioms wG1BFL2_eq

/-- `Gstar := G₁ = gOneOfNeumann wG0BFL2 wPBFL2` (`= 2•1`, §5a). -/
noncomputable def GstarBFL2 : BFL2 witnessL →L[ℝ] BFL2 witnessL := gOneOfNeumann wG0BFL2 wPBFL2

/-- `Ginv := (1/2)•1`, the two-sided inverse of `GstarBFL2` (verified below, not asserted). -/
noncomputable def GinvBFL2 : BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  (1 / 2 : ℝ) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)

theorem GinvBFL2_GstarBFL2 (x : BFL2 witnessL) : GinvBFL2 (GstarBFL2 x) = x := by
  unfold GinvBFL2 GstarBFL2; rw [wG1BFL2_eq]
  show (1 / 2 : ℝ) • ((2 : ℝ) • x) = x
  rw [smul_smul]; norm_num

theorem GstarBFL2_GinvBFL2 (x : BFL2 witnessL) : GstarBFL2 (GinvBFL2 x) = x := by
  unfold GinvBFL2 GstarBFL2; rw [wG1BFL2_eq]
  show (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
  rw [smul_smul]; norm_num

theorem GinvBFL2_selfAdjoint (x y : BFL2 witnessL) :
    (inner ℝ (GinvBFL2 x) y : ℝ) = inner ℝ x (GinvBFL2 y) := by
  unfold GinvBFL2
  show (inner ℝ ((1 / 2 : ℝ) • x) y : ℝ) = inner ℝ x ((1 / 2 : ℝ) • y)
  rw [real_inner_smul_left, real_inner_smul_right]

theorem GinvBFL2_posSemidef (x : BFL2 witnessL) : (0 : ℝ) ≤ inner ℝ x (GinvBFL2 x) := by
  unfold GinvBFL2
  show (0 : ℝ) ≤ inner ℝ x ((1 / 2 : ℝ) • x)
  rw [real_inner_smul_right]
  have h : (0 : ℝ) ≤ (inner ℝ x x : ℝ) := real_inner_self_nonneg
  linarith

#print axioms GinvBFL2_GstarBFL2
#print axioms GstarBFL2_GinvBFL2
#print axioms GinvBFL2_selfAdjoint
#print axioms GinvBFL2_posSemidef

/-- ⚠⚠ **`Q := 1` ⇒ NO SCHUR COMPLEMENT. THIS IS NOT `Δ_k`.** (F4, see the correction banner at the
top of this file for the full what-remains-true / what-does-not-transfer list.) `CompInv` is
`BalabanCovarianceData`'s own `(Q G₁ Q*)⁻¹` slot; with `Q = Qstar = 1` and `GstarBFL2 = 2 • 1` it is
literally `(1/2) • 1`, so `deltaKForm`'s leading term is `(1/2)‖B‖²`. Every downstream
`U`-independence and first-two-terms-coercivity statement is FORCED by that, and none of them is
evidence about (3.156). Statements about the SUBSPACE (`subspace156BFL2`) are unaffected.

§5b — **`Q := Qstar := 1` (identity), a DISCLOSED simplification, matching
`CarrierBridge.lean`'s OWN precedent for exactly this situation** (`carrierBridgeFamily`'s
`Q := 1, Qstar := 1, Q1 := 0`, disclosed there as "every field beyond `LambdaSmall` is a genuine,
honestly-disclosed placeholder"). Since `H = K = BFL2 witnessL` here (§4's own disclosed
simplification), `Q := 1` is consistent with (though not forced by) that collapse — a genuine,
non-identity `Q` would need a SECOND, smaller real carrier and a real block-averaging map, not
attempted here. `Comp := Q(Gstar(Qstar ·)) = Gstar` follows by `rfl` once `Q = Qstar = 1`. -/
noncomputable def deltaKUnifiedData : BalabanCovarianceData (BFL2 witnessL) (BFL2 witnessL) where
  Ginv := GinvBFL2
  Gstar := GstarBFL2
  Ginv_Gstar := GinvBFL2_GstarBFL2
  Gstar_Ginv := GstarBFL2_GinvBFL2
  Ginv_selfAdjoint := GinvBFL2_selfAdjoint
  Ginv_posSemidef := GinvBFL2_posSemidef
  Q := 1
  Qstar := 1
  Q_Qstar_adjoint := fun _ _ => rfl
  Comp := GstarBFL2
  Comp_eq := fun _ => rfl
  CompInv := GinvBFL2
  Comp_CompInv := GstarBFL2_GinvBFL2
  CompInv_Comp := GinvBFL2_GstarBFL2

#print axioms deltaKUnifiedData

open AdalyFormal.Balaban.DeltaKAssembly (deltaKForm)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.DeltaKAssemblyRepaired (deltaKFormOnSubspace)

/-- **THE DELIVERABLE: `deltaKForm` restricted to `subspace156`, ONE well-typed object, on ONE
carrier `BFL2 witnessL`.** Literally `DeltaKAssemblyRepaired.deltaKFormOnSubspace` (REUSED, not
rebuilt, LAW-19) applied to `deltaKUnifiedData` and `subspace156BFL2` — both now on the SAME type,
so this typechecks where `DeltaKAssemblyRepaired.lean` §6b's own residual note said it could not.
`Qext`/`J`/`bc` remain the SAME disclosed external parameters `DeltaKAssembly.lean` §0 already names
(unchanged by this file, per the dispatch's coercivity-not-claimed scope). -/
noncomputable def deltaKFormOnSubspace156 (bc : BaseConstant)
    (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (B : subspace156BFL2 Lambda S' ell U) : ℝ :=
  deltaKFormOnSubspace deltaKUnifiedData bc Qext J (subspace156BFL2 Lambda S' ell U) B

theorem deltaKFormOnSubspace156_eq (bc : BaseConstant)
    (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (B : subspace156BFL2 Lambda S' ell U) :
    deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B =
      deltaKForm deltaKUnifiedData bc Qext J (B : BFL2 witnessL) := rfl

#print axioms deltaKFormOnSubspace156
#print axioms deltaKFormOnSubspace156_eq

/-- **THE HEADLINE, evaluated at the concrete non-vacuous witness `subspace156BFL2_ne_bot` exhibits**
— `deltaKFormOnSubspace156` genuinely applies to a NONZERO member of the subspace, not merely to `0`
(the trivial case every `Submodule` restriction admits vacuously). This is the final assembly step:
combining §3 (`subspace156BFL2 ≠ ⊥`) and §4 (the well-typed restricted form) into one usable term. -/
noncomputable example (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) : ℝ :=
  deltaKFormOnSubspace156 bc Qext J Finset.univ ∅ witnessEll (trivialU witnessL)
    ⟨(bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo, by
      show (bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo ∈
        subspace156BFL2 Finset.univ ∅ witnessEll (trivialU witnessL)
      show checkerConfigSuTwo ∈ subspace156G Finset.univ ∅ witnessEll (trivialU witnessL)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro b hb; exact absurd (Finset.mem_univ b.1) hb
      · intro y hy; exact absurd hy (Finset.notMem_empty y)
      · exact checkerConfigSuTwo_mem_q1RealKernel_trivialU⟩

/-! ## §5 — WHAT REMAINS OPEN, named precisely (propagation target, `problem/PROBLEM.md` disposition)

1. **Coercivity** (`deltaKForm ≥ 0` on `subspace156BFL2`, or any bound) — NOT claimed anywhere in
   this file, exactly the dispatch's own scope limit. Phase 2's actual target.
2. **`H ≠ K`** (Fine ≠ Coarse) — collapsed to ONE carrier here (§4's own disclosure); a faithful
   version needs a second, smaller real carrier and a genuine block-averaging `Q`, not attempted.
3. **`subspace156BFL2 ≠ ⊥` at a non-trivial `S'`/proper `Lambda`** — open (§3's closing note); the
   proved witness uses `S' = ∅`, `Lambda = Finset.univ`, both forced/convenient degeneracies of the
   SPECIFIC witness `checkerConfigSuTwo`, not evidence against a less-degenerate joint witness
   existing (nor evidence for one).
4. **`Q1Real` at a non-flat `U`** — `checkerConfigSuTwo`'s kernel-membership is proved only at
   `trivialU` (`Q1Real.lean`'s own disclosure); this file's `subspace156BFL2_ne_bot` inherits that
   restriction unchanged, not attempted to lift here.
-/

end AdalyFormal.Balaban.DeltaKUnified
