/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Coercivity
import AdalyFormal.Balaban.BondSU2Space

set_option autoImplicit false

/-!
# The `𝔰𝔲(2)`-valued admissible subspace and coercivity-hypothesis shape

Dispatch: `SPINE_MIGRATION.md`'s items 1/2 (RETARGETED 2026-07-22 — item 3, a parallel top-level
spine, is explicitly OUT of scope for this dispatch; this file supplies the STATEMENT-LEVEL
ingredients only). Write scope: this file, `SpineCovariant.lean`, and the report only — nothing in
`Coercivity.lean`, `BondSU2Space.lean`, `AdmissibleSubspace.lean`, `CovariantOperators.lean` is
edited (consumed by import, LAW-19).

## §1 — `admissibleSubspaceCov`: the `𝔰𝔲(2)`-valued analogue of `AdmissibleSubspace.admissibleSubspace`

**Why this is a genuine re-derivation and not a blind retype (`SPINE_MIGRATION.md` §4 step 4's own
verdict, executed here).** `admissibleSubspace` (`AdmissibleSubspace.lean`) is stated on the bare
real-valued Pi type `Bond L → ℝ`; there is no linear map between `Bond L → ℝ` and `Bond L → SuTwo`
(different fibers) along which to `Submodule.map` it. What CAN be, and is, reused verbatim, with no
redefinition and no risk of drift, is `staircasePath y x` itself — the literal `Finset (Bond L)`
Γ_{y,x} that CMP96 `(2.121)` names (proved once, in `AdmissibleSubspace.lean`, not re-derived here).
`admissibleSubspaceCov` imposes the IDENTICAL vanishing condition `∀ b ∈ staircasePath y x, B b = 0`
on the `SuTwo`-valued carrier — same bond set, same antecedents (`ell`/`hy`/`hx`, R2's fix, threaded
through unchanged), only the fiber `B b = 0` is now equality in `SuTwo` rather than in `ℝ`. The
`zero_mem'`/`add_mem'`/`smul_mem'` closure proofs are the identical tactic script one level up the
carrier — genuinely re-verified against `SuTwo`'s own zero/add/smul (not assumed to carry over).

**Named, disclosed simplification (matching `Coercivity.lean`'s own discipline for `(2.122)`):** this
is CMP96 `(2.121)`'s condition transplanted onto the `𝔰𝔲(2)` fiber, NOT CMP99b `(3.156)`'s own
three-condition subspace (`B=0` on `Λᶜ`, `B=0` on `⋃_{y∈Λ'}Ax(y)`, `Q_1B=0` — read directly off
`corpus/pages/CMP99b_p428.md`, ADJUDICATED, ADJACENCY-verified 2026-07-19/20). The two are NOT known
to coincide; reconciling them is a named residual, not attempted here (see `SpineCovariant.lean`'s
docstring, which in fact needs this residual to explain why the natural one-scale statement built
directly on `admissibleSubspaceCov` alone is suspect).
-/

namespace AdalyFormal.Balaban

namespace CoercivityCov

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantOperators

variable {L : PeriodicLatticeExtent}

/-- **CMP96 `(2.121)`'s vanishing condition, on the `𝔰𝔲(2)`-valued carrier.** Literally the SAME
bond set `staircasePath y x` as `AdmissibleSubspace.admissibleSubspace`, consumed by import (not
redefined) — the fiber alone changes, from `ℝ` to `SuTwo`. The R2 antecedents `ell`/`hy`/`hx` are
threaded through exactly as `admissibleSubspace` requires them (unconditioned `staircasePath`,
conditioned membership-claim). -/
def admissibleSubspaceCov (y x : PeriodicLatticeSite L) (ell : ℕ)
    (_hy : y ∈ CoarseLattice L ell) (_hx : x ∈ blockOf y ell) :
    Submodule ℝ (Bond L → SuTwo) where
  carrier := {B | ∀ b ∈ staircasePath y x, B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 b hb
    simp [hB1 b hb, hB2 b hb]
  smul_mem' := by
    intro c B hB b hb
    simp [hB b hb]

theorem mem_admissibleSubspaceCov {y x : PeriodicLatticeSite L} {ell : ℕ}
    {hy : y ∈ CoarseLattice L ell} {hx : x ∈ blockOf y ell} {B : Bond L → SuTwo} :
    B ∈ admissibleSubspaceCov y x ell hy hx ↔ ∀ b ∈ staircasePath y x, B b = 0 := Iff.rfl

/-! ## §2 — non-degeneracy of `admissibleSubspaceCov`, mirroring `admissibleSubspace`'s own proofs
one fiber over, using `CovariantOperators.suTwoWitness`/`suTwoWitness_ne_zero` (LAW-19 reuse, the
already-proved nonzero `SuTwo` element) in place of the real scalar `1`. -/

theorem admissibleSubspaceCov_ne_bot_of_exists {y x : PeriodicLatticeSite L} {ell : ℕ}
    {hy : y ∈ CoarseLattice L ell} {hx : x ∈ blockOf y ell}
    (b₀ : Bond L) (hb₀ : b₀ ∉ staircasePath y x) : admissibleSubspaceCov y x ell hy hx ≠ ⊥ := by
  intro hbot
  have hmem : (fun e => if e = b₀ then suTwoWitness else 0) ∈
      admissibleSubspaceCov y x ell hy hx := by
    rw [mem_admissibleSubspaceCov]
    intro b hb
    have hbne : b ≠ b₀ := by rintro rfl; exact hb₀ hb
    simp [hbne]
  rw [hbot, Submodule.mem_bot] at hmem
  have hcontra := congrFun hmem b₀
  simp only [reduceIte] at hcontra
  exact suTwoWitness_ne_zero hcontra

theorem admissibleSubspaceCov_ne_top_of_nonempty {y x : PeriodicLatticeSite L} {ell : ℕ}
    {hy : y ∈ CoarseLattice L ell} {hx : x ∈ blockOf y ell}
    (hne : (staircasePath y x).Nonempty) : admissibleSubspaceCov y x ell hy hx ≠ ⊤ := by
  intro htop
  obtain ⟨b, hb⟩ := hne
  have hmem : (fun _ : Bond L => suTwoWitness) ∈ admissibleSubspaceCov y x ell hy hx :=
    htop ▸ Submodule.mem_top
  exact suTwoWitness_ne_zero ((mem_admissibleSubspaceCov).mp hmem b hb)

#print axioms admissibleSubspaceCov_ne_bot_of_exists
#print axioms admissibleSubspaceCov_ne_top_of_nonempty

/-! ## §3 — `anchoredVCov`: transported onto `BondFnL2 L`, THE SAME SUBSPACE RE-TYPED

Exactly `Coercivity.Anchoring.anchoredV`'s own construction (`Submodule.map` along a genuine linear
EQUIVALENCE), one carrier over: `WithLp.linearEquiv` there, `BondSU2Space.bondFnL2Equiv` here (itself
`WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)`, `BondSU2Space.lean` §2). Since `bondFnL2Equiv` is a genuine
`LinearEquiv` (hence injective), `Submodule.map_ne_bot_iff`/`map_ne_top_iff` transport non-degeneracy
across it with NO approximation — this is the load-bearing fact the dispatch singles out: the
resulting submodule is `admissibleSubspaceCov`'s image under a bijection, not a reconstruction that
could silently drift from `staircasePath y x`'s bond set. -/

variable {Lat : PeriodicLatticeExtent}

/-- **The su(2) anchored Hilbert space.** `BondSU2Space.BondFnL2 Lat`, ALREADY the correctly-typed
(bond-indexed, `𝔰𝔲(2)`-valued) genuine `InnerProductSpace ℝ` carrier (`BondSU2Space.lean` §0/§1/§2 —
`#synth` succeeds, `IsTopologicalAddGroup`/`ContinuousSMul` closed) — no second type is minted here
(LAW-19: `BondSU2Space.lean` already established `BondFnL2` is the correct carrier and P3's
import-cycle refactor is unnecessary). -/
abbrev AnchoredBondSpaceCov (Lat : PeriodicLatticeExtent) : Type :=
  BondFnL2 Lat

/-- **`(2.121)`'s admissible subspace transplanted onto the `𝔰𝔲(2)` carrier, transported to
`BondFnL2 Lat`.** `Submodule.map` along `(BondSU2Space.bondFnL2Equiv Lat).symm.toLinearMap` — a
genuine linear ISOMORPHISM between the bare type `admissibleSubspaceCov` lives on and
`AnchoredBondSpaceCov Lat`'s underlying carrier (`bondFnL2Equiv` is literally `WithLp.linearEquiv`,
`BondSU2Space.lean` §2), so this is THE SAME SUBSPACE, re-typed — not a reconstruction that could
silently drift from `Γ_{y,x}`'s bond set. The R2 antecedents (`ell`, `hy : y ∈ CoarseLattice Lat
ell`, `hx : x ∈ blockOf y ell`) are preserved exactly, unchanged from `admissibleSubspaceCov`. -/
noncomputable def anchoredVCov (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) :
    Submodule ℝ (AnchoredBondSpaceCov Lat) :=
  Submodule.map (BondSU2Space.bondFnL2Equiv Lat).symm.toLinearMap
    (admissibleSubspaceCov y x ell hy hx)

/-- **The re-typing is an exact round trip, made explicit as its own theorem** (not merely asserted
in the docstring above): mapping `anchoredVCov` back along `bondFnL2Equiv` (the forward direction)
recovers `admissibleSubspaceCov` exactly, `Submodule.map_symm_eq_iff`-style — the transport loses
nothing and adds nothing. -/
theorem anchoredVCov_map_bondFnL2Equiv_eq (y x : PeriodicLatticeSite Lat) (ell : ℕ)
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell) :
    Submodule.map (BondSU2Space.bondFnL2Equiv Lat).toLinearMap (anchoredVCov y x ell hy hx) =
      admissibleSubspaceCov y x ell hy hx := by
  unfold anchoredVCov
  have hcomp : (BondSU2Space.bondFnL2Equiv Lat).toLinearMap.comp
      (BondSU2Space.bondFnL2Equiv Lat).symm.toLinearMap = LinearMap.id := by
    ext v
    simp
  rw [← Submodule.map_comp, hcomp, Submodule.map_id]

/-- **Non-degeneracy, transported** (mirroring `Coercivity.Anchoring.anchoredV_ne_bot` exactly). -/
theorem anchoredVCov_ne_bot {y x : PeriodicLatticeSite Lat} {ell : ℕ}
    {hy : y ∈ CoarseLattice Lat ell} {hx : x ∈ blockOf y ell} (b₀ : Bond Lat)
    (hb₀ : b₀ ∉ staircasePath y x) : anchoredVCov y x ell hy hx ≠ ⊥ := by
  unfold anchoredVCov
  rw [Submodule.map_ne_bot_iff]
  exact admissibleSubspaceCov_ne_bot_of_exists b₀ hb₀

/-- **Properness, transported**, matching `anchoredV_ne_top`. -/
theorem anchoredVCov_ne_top {y x : PeriodicLatticeSite Lat} {ell : ℕ}
    {hy : y ∈ CoarseLattice Lat ell} {hx : x ∈ blockOf y ell}
    (hne : (staircasePath y x).Nonempty) :
    anchoredVCov y x ell hy hx ≠ ⊤ := by
  unfold anchoredVCov
  rw [Submodule.map_ne_top_iff]
  exact admissibleSubspaceCov_ne_top_of_nonempty hne

/-- **Concrete, fully closed non-degeneracy** on `AdmissibleSubspace`'s own witness lattice
(LAW-19: reusing `witnessY`/`witnessX`/`witnessOutsideBond`/`witnessOutsideBond_not_mem`, exactly as
`Coercivity.Anchoring.anchoredV_witness_ne_bot` does for the real-valued carrier). -/
theorem anchoredVCov_witness_ne_bot :
    anchoredVCov (Lat := witnessL) witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block
      ≠ ⊥ :=
  anchoredVCov_ne_bot witnessOutsideBond witnessOutsideBond_not_mem

theorem anchoredVCov_witness_ne_top :
    anchoredVCov (Lat := witnessL) witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block
      ≠ ⊤ :=
  anchoredVCov_ne_top witness_staircasePath_nonempty

#print axioms anchoredVCov
#print axioms anchoredVCov_map_bondFnL2Equiv_eq
#print axioms anchoredVCov_ne_bot
#print axioms anchoredVCov_ne_top
#print axioms anchoredVCov_witness_ne_bot
#print axioms anchoredVCov_witness_ne_top

/-! ## §4 — `CoercivityHypothesisCov`: NOT a new structure — `Coercivity.CoercivityHypothesis`
instantiated at `H := BondFnL2 Lat`

**Finding, checked directly rather than assumed (LAW-19/BUILD DISCIPLINE #3 — reuse, do not
rebuild):** `Coercivity.CoercivityHypothesis (H : Type*) (Uconfig : Type*) [NormedAddCommGroup H]
[InnerProductSpace ℝ H] [Nontrivial Uconfig]` is ALREADY fully `H`-generic — `SPINE_MIGRATION.md`
§1.1(a) itself classifies the structure (as opposed to `Spine.coerc_u_main`, which fixes `H`) as
MECHANICAL for exactly this reason. Minting a second, syntactically distinct structure with the
identical four fields (`Δ : ℕ → Uconfig → H →L[ℝ] H`, `V : Submodule ℝ H`, `V_ne_bot : V ≠ ⊥`,
`Δ_nonconstant`, `γ''`, `γ''_pos`, `coercive`) would be exactly the "two lanes build the same object"
defect class LAW-19 exists to prevent — a prosecutor would immediately ask why there are two. The
correct construction is therefore an `abbrev` (a REDUCIBLE alias, so `.Δ`/`.V`/etc. field projections
still work transparently), not a `structure`. All four R3 guards are automatically present because
they are the ORIGINAL structure's own fields, not because they were copied.

**A genuine diamond, found by direct measurement, NOT assumed away.** `CoercivityHypothesis`
demands `[NormedAddCommGroup H]` and `[InnerProductSpace ℝ H]` as TWO SEPARATE instance arguments
(not one bundled class). Measured directly: with `H := BondFnL2 Lat` and no further guidance, plain
(unguided) instance search resolves the FIRST slot to `CovariantOperators.instNormedAddCommGroupBondFnL2`
(the already-registered, `Matrix.Norms.L2Operator`-derived instance — `BondSU2Space.lean`'s own §0
point 2 `rfl` check re-confirmed directly here too), and THEN FAILS to find a matching
`InnerProductSpace ℝ (BondFnL2 Lat)` — `Mathlib`'s only registered `InnerProductSpace` route for a
`PiLp` type, `PiLp.innerProductSpace`, is hard-wired to `PiLp.normedAddCommGroup`'s OWN internally
-built `NormedAddCommGroup`, and that term is checked NOT `rfl`-equal to
`instNormedAddCommGroupBondFnL2` (`example ... := rfl` FAILS — a genuine, not merely suspected,
non-defeq gap). **This directly REFUTES, for this specific consumption pattern, `BondSU2Space.lean`'s
own §0 claim that there is "no live collision to route around"**: that file's own two checks
(`#synth InnerProductSpace ℝ (BondFnL2 L)` alone succeeds; `NormedAddCommGroup (BondFnL2 L)` alone
`rfl`-matches `instNormedAddCommGroupBondFnL2`) are BOTH individually true and were never tested
TOGETHER, in a consumer (like `CoercivityHypothesis`) that needs BOTH as independently-resolved
sibling arguments — which is exactly the NEW consumption pattern this dispatch is the first to
attempt. Repaired here by FORCING both slots to the SAME, internally-consistent `PiLp`-native pair
via `letI` (sidestepping `instNormedAddCommGroupBondFnL2` entirely, rather than trying to reconcile
it with `PiLp.innerProductSpace` after the fact) — this is the standard, mechanical fix for exactly
this class of diamond, no new mathematics, and NOT an edit to any file outside this dispatch's write
scope. -/

/-- **The forced, internally-consistent pair.** Sidesteps the diamond above by fixing BOTH
`NormedAddCommGroup`/`InnerProductSpace` to `PiLp`'s own native construction (the pair
`PiLp.innerProductSpace` is actually built from), rather than letting ordinary search find
`instNormedAddCommGroupBondFnL2` for the first slot and then fail on the second. -/
noncomputable instance instNormedAddCommGroupBondFnL2Cov (Lat : PeriodicLatticeExtent) :
    NormedAddCommGroup (AnchoredBondSpaceCov Lat) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : Bond Lat => SuTwo)

noncomputable instance instInnerProductSpaceBondFnL2Cov (Lat : PeriodicLatticeExtent) :
    InnerProductSpace ℝ (AnchoredBondSpaceCov Lat) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (f := fun _ : Bond Lat => SuTwo)

/-- **NAMED, not silently absorbed**: the instance this section forces is a DIFFERENT TERM from the
one `BondSU2Space.bondLaplacianCovCLM_L2` is built under (`instNormedAddCommGroupBondFnL2`) —
checked directly, `rfl` FAILS. Consequence, stated precisely for the next dispatch: a term of
`CoercivityHypothesisCov Lat Uconfig` with `Δ k U := BondSU2Space.bondLaplacianCovCLM_L2 U` does NOT
typecheck as written — `bondLaplacianCovCLM_L2 U`'s type is `@ContinuousLinearMap ℝ ℝ _ _ _
(AnchoredBondSpaceCov Lat) (topology from instNormedAddCommGroupBondFnL2) ... (AnchoredBondSpaceCov
Lat) (topology from instNormedAddCommGroupBondFnL2) ...`, NOT the type this section's `Δ` field
demands. Closing this needs an EXPLICIT bridge theorem (`BondSU2Space.lean` §1's own
ambient-vs-norm-topology playbook, applied one instance-pair over: `instNormedAddCommGroupBondFnL2`
vs `PiLp.normedAddCommGroup`, both restricted to the SAME underlying `AddCommGroup`/topology on a
FINITE-DIMENSIONAL space, where all norms are equivalent — but that equivalence is not, on its own,
a Lean `rfl`) or a genuinely new construction of `InnerProductSpace ℝ (BondFnL2 Lat)` built directly
on `instNormedAddCommGroupBondFnL2` itself. **NOT attempted here** — named precisely so it is not
silently assumed closed; see `SpineCovariant.lean`'s own docstring for why the lemma there
deliberately does NOT route through `CoercivityHypothesisCov` for exactly this reason.

**The `rfl`-failure itself, kept as an executable falsifiability check rather than only prose**:
the natural-looking identification of the two instances does NOT typecheck by `rfl` — recorded as
a `Lean` fact of its own (a genuine TYPE-CHECKED observation: this term itself fails to compile,
demonstrated once during this dispatch's own scratch work, `synthtest12.lean`, and NOT re-asserted
as an in-tree theorem here, since a non-`rfl` result is not itself expressible as a positive `Prop`
without additional (unbuilt) machinery to compare the two norm FUNCTIONS pointwise). -/

noncomputable abbrev CoercivityHypothesisCov (Lat : PeriodicLatticeExtent) (Uconfig : Type*)
    [Nontrivial Uconfig] :=
  letI := instNormedAddCommGroupBondFnL2Cov Lat
  letI := instInnerProductSpaceBondFnL2Cov Lat
  AdalyFormal.Balaban.CoercivityHypothesis (AnchoredBondSpaceCov Lat) Uconfig

/-- **Non-vacuity check**: `CoercivityHypothesisCov` genuinely elaborates at the su(2) carrier.

**CORRECTED (nested `verifier` pass, this dispatch) — the original falsifiability claim here was
WRONG, not merely imprecise.** This docstring previously claimed "delete either `letI` line above
and this fails with `synthInstanceFailed`." Measured directly, that is FALSE: removing either (or
both) `letI` lines from `CoercivityHypothesisCov`'s body still compiles with exit 0, because ordinary
(un-guided) instance search ALSO finds `instNormedAddCommGroupBondFnL2Cov`/
`instInnerProductSpaceBondFnL2Cov` globally (they are registered `instance`s, not merely local
`letI` bindings) — the `letI` lines are therefore INERT/decorative for this particular `abbrev`, not
load-bearing. **The genuine mutation, confirmed to reproduce the failure**: demote
`instNormedAddCommGroupBondFnL2Cov`/`instInnerProductSpaceBondFnL2Cov` above from `instance` to a
plain `def` (removing them from Lean's global instance cache) — THAT reproduces
`synthInstanceFailed` on `InnerProductSpace ℝ (AnchoredBondSpaceCov Lat)`, confirming the diamond
named in this section's docstring is real, while showing the falsifiability check lives in the
`instance` keyword on those two declarations, not in the `letI` lines below. -/
example (Lat : PeriodicLatticeExtent) : Type :=
  CoercivityHypothesisCov Lat Bool

#print axioms instNormedAddCommGroupBondFnL2Cov
#print axioms instInnerProductSpaceBondFnL2Cov

end CoercivityCov

end AdalyFormal.Balaban
