/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKUnified
import AdalyFormal.Balaban.BondSU2Space

set_option autoImplicit false
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 1000000

/-!
# `NonDegenerateInstances.lean` — `2 ≤ dim (3.156)-subspace`, UNIFORMLY IN `U`, by rank–nullity

**Dispatch target** (`compute/REGISTRY_CAVEAT_SWEEP.md` Tier-1 item 2, the coupled hole): two
independently-recorded caveats compose into one blocker.

* `DeltaKUnified.subspace156BFL2_ne_bot`'s registry verdict is caveated **"only at trivialU"** — its
  witness is `Q1Real.checkerConfigSuTwo`, whose kernel membership is itself proved only at
  `trivialU` (`Q1Real.lean` §9's own disclosure: at a non-flat background the two `rZeroA_ell2`
  addends carry DIFFERENT transports, so the raw pointwise cancellation does not transfer).
* `FaithfulDeltaKNonScalar.lean` §"WHAT THIS FILE DOES NOT CLOSE" item 1 records separately that
  `subspace156BFL2_ne_bot` *"only gives `dim V ≥ 1`"*, and that a non-scalarity conjunct needs
  `dim V ≥ 2` because **on a 1-dimensional space every operator IS scalar**.

So the composite: a non-scalarity clause could not be stated on `V`, and `V` was only known nonzero
at `U = 1`.

## WHAT IS PROVED HERE

**`2 ≤ Module.finrank ℝ (subspace156BFL2 Λ S' ell U)` — for EVERY `U`, with no flatness,
regularity, or witness hypothesis whatsoever** (§4), under an explicit and checkable combinatorial
hypothesis on `Λ` and `S'` alone. The route is RANK–NULLITY, not a witness: `subspace156G` is the
kernel of ONE explicit linear map (§2, `clauseMap` — the three `(3.156)` clauses assembled by
`LinearMap.prod`), whose codomain has strictly smaller real dimension than its domain, and the
deficit is enormous:

| space | real dimension |
|---|---|
| domain `Bond witnessL → SuTwo` (`= BFL2 witnessL`) | `192 · dim 𝔰𝔲(2)` |
| `Q₁`-clause codomain `CoarseBond witnessL 2 → SuTwo` | `24 · dim 𝔰𝔲(2)` |
| `Λᶜ`-clause codomain | `#(bonds based outside Λ) · dim 𝔰𝔲(2)` |
| `Ax`-clause codomain | `#(⋃_{y∈S'} Ax(y,ell)) · dim 𝔰𝔲(2)` |

(`192 = 4³ · 3` fine bonds and `24 = 2³ · 3` coarse bonds are computed in §1, by `decide`, not
assumed. `dim 𝔰𝔲(2) ≥ 1` is proved from `suTwoWitness ≠ 0`, §1; the exact value `3` is never
needed and never used, so every bound below is stated in terms of `Module.finrank ℝ SuTwo` itself and
holds whatever that value is.)

At `Λ := univ`, `S' := ∅` the two locus clauses are `⊤` and the bound is
`168 · dim 𝔰𝔲(2) ≤ dim V` (§4). At the genuinely non-degenerate parameters
`Λ := univ.erase witnessY` (PROPER), `S' := {witnessY}` (NONEMPTY), `ell := 2`, `U` arbitrary
(including the tree's non-flat `CovariantOperators.witnessU`) it is ~~`158 · dim 𝔰𝔲(2) ≤ dim V` (§5)~~
— **`161 · dim 𝔰𝔲(2) ≤ dim V`, §8's deduplicated count (S75): the `158` charges the two locus clauses
`3 + 7` while they overlap, `outsideBonds ⊆ axBonds` at this point, so the honest charge is `7`. §5's
`158` statement remains in the file and remains TRUE, merely not sharp.**

**This is the primitive `RegularUDomainWitness.lean` §7 item 2 named as missing** — verbatim:
*"plus `Submodule.finrank` machinery — `finrank (Bond → SuTwo)`, `finrank_le_of_surjective`-style
rank bounds, and a `finrank` lower bound for an intersection — none of which exists in this tree for
these carriers"*. It exists now, for exactly these carriers, and it is `U`-uniform, which is the
property that file's residual `[REGU-DOMAIN-NONVAC-GENERALU]` actually wanted.

## THE HYPOTHESIS IS DOING REAL WORK — the must-not-fire control (§3b)

`DeltaKUnified.subspace156BFL2_eq_bot_of_lambda_empty` proves the subspace IS `⊥` at `Λ := ∅`. So a
dimension bound that fired there would be FALSE. It does not: at `Λ := ∅` every one of the 192 bonds
is "outside `Λ`", the cardinality hypothesis reads `192 + … + 26 ≤ 192`, and it is refuted by
`decide` (§3b, `cardHyp_fails_at_lambda_empty`). The `≠ ⊥` control and the positive bound are
therefore separated by exactly the hypothesis, not by luck.

## WHAT THIS DOES **NOT** SAY (stated, not hidden)

1. **It is a statement about the SUBSPACE only**, which is precisely the axis `DeltaKUnified.lean`'s
   own F4 correction banner lists as unaffected by `Q := 1` (*"§3's `subspace156BFL2 ≠ ⊥` … are
   statements about the **subspace only**. They never mention the form, and the subspace IS built
   from the real `Q1Real.q1RealKernel U`"*). Nothing here is evidence about `Δ_k`, whose form on this
   carrier remains the disclosed-scalar artifact.
2. **§4 itself supplies no NAMED member.** Rank–nullity gives dimension, not vectors. §6 therefore
   also builds explicit named members — `checkerDirSuTwo μ` for each of the three directions, three
   pairwise linearly independent kernel elements — but those, like `checkerConfigSuTwo` whose proof
   they generalize, are proved to lie in the kernel ONLY at `trivialU`. The `U`-uniform statement is
   the dimension bound; the named-member statement is the flat-background one. Both are stated at
   their own true scope and neither is upgraded to the other's.
3. ~~**It does not prove non-scalarity of anything.** `dim V ≥ 2` is the PREREQUISITE
   `FaithfulDeltaKNonScalar.lean` named as missing; the non-scalarity statement itself needs, in
   addition, witnesses in `V` that distinguish an operator's action, which is a separate build.~~
   **SUPERSEDED by §7 in this same pass** (struck text retained, not deleted): §7 DOES prove
   non-scalarity of the curl/Gram operator `D_U D_U^*` on the admissible subspace, in two halves —
   every NONZERO `c` for EVERY `U` by dimension (§7b), and every `c` including `0` at `trivialU` by
   an explicit admissible witness (§7c). ~~The one case NOT closed is `c = 0` at a non-flat `U`; §7's
   own header states the exact reduction and the two candidate missing primitives with the arithmetic
   each would yield.~~ **SUPERSEDED (S75): §7d closes `c = 0` at `Λ := univ`, `S' := ∅` for every `U`,
   and §8 closes it at a PROPER `Λ` and a NONEMPTY `S'` for every `U`, and generally under an explicit
   decidable hypothesis on `Λ`, `S'`, `ell` (`bondLaplacianCov_not_scalar_of_card_union`,
   `bondLaplacianCov_not_scalar_general_union`).** The `C`-SANDWICHED form
   (`RD.Cadj ∘ Base ∘ RD.C`) is still not addressed — §7 is
   about the curl term itself, which is where `FaithfulDeltaKNonScalar.lean` locates the
   non-scalarity.
4. **`ell` is inert at `S' = ∅`.** `subspace156G`'s `ell` argument enters only through
   `AxUnionLocusG S' ell`, so §4's bound says nothing about `ell`; and at `ell ∈ {0,1}`
   `Ax witnessY ell = ∅` (§5b, by `decide`) — a §DEGEN point where clause 2 is vacuous, recorded so
   no consumer reads §5 as evidence at small `ell`.

## §7, THE FOLLOW-ON THAT `dim V ≥ 2` UNLOCKS (same pass)

`FaithfulDeltaKNonScalar.lean` item 1 named `dim V ≥ 2` as one of TWO prerequisites for a
non-scalarity statement on `V`; the other was an admissible witness distinguishing the curl term.
§7 supplies the second and proves the consequence:

* `bondLaplacianCov_not_nonzero_scalar_on_subspace156G` — `D_U D_U^* ≠ c·id` on `V` for every
  `c ≠ 0` and **every `U`**, by dimension alone (`dim ker D_U^* ≥ 128·dim 𝔰𝔲(2)` versus
  `dim V ≥ 168·dim 𝔰𝔲(2)`, and `128 + 168 > 192`).
* `bondLaplacianCov_not_scalar_on_subspace156G_trivialU` — every `c`, at `trivialU`, via the explicit
  admissible witness `signDir01SuTwo`.

* `bondLaplacianCov_not_scalar_on_subspace156G_univ_empty` — **every `c` INCLUDING `0`, at EVERY
  `U`**, at `Λ := univ`, `S' := ∅`: §7d closes the `c = 0` case by proving
  `ker (D_U D_U^*) = ker D_U^*` (definiteness of `covSiteInner`, from the tree's pre-existing
  `hsInner_self_eq_zero`) and `rank D_U^* ≥ 32 · dim 𝔰𝔲(2)` (a 32-bond scatter using no property of
  `U`), so `dim ker D_U^* ≤ 160 · dim 𝔰𝔲(2) < 168 · dim 𝔰𝔲(2) ≤ dim V`.

~~Not closed: `c = 0` at the §5 NON-DEGENERATE parameter point, where `dim V ≥ 158 · dim 𝔰𝔲(2)` and the
32-bond scatter gives only `160 · dim 𝔰𝔲(2)` — one notch short. §7d's header states the exact
refinement (48 bonds, triangular) that closes the gap and is not built.~~

⚠ **SUPERSEDED BY §8 (struck text retained, not deleted, S75).** `c = 0` at the §5 NON-DEGENERATE
parameter point is CLOSED — `bondLaplacianCov_not_scalar_nondegenerate`, every `c`, every `U`, at a
PROPER `Λ` and a NONEMPTY `S'` — and closed four independent ways. The `158` above is not false but
is NOT SHARP: §3's `ClauseCod` charges the two locus clauses `3 + 7` while they OVERLAP (all three
`Λ`-forbidden bonds are axial; `outsideBonds_subset_axBonds_nondegenerate`, `decide`), so the
deduplicated count is `7` and the true bound is `161 · dim 𝔰𝔲(2) ≤ dim V`
(`finrank_subspace156G_nondegenerate_sharp`) — which already beats the pre-existing
`160 · dim 𝔰𝔲(2)` with no new geometry. The 48-bond triangular refinement is ALSO built (§8), giving
`dim ker D_U^* ≤ 144 · dim 𝔰𝔲(2)`, and §8 further supplies a criterion with NO global cardinality
hypothesis at all, plus a proof of exactly where dimension counting against `ker D_U^*` saturates.

**Does not edit** `DeltaKUnified.lean`, `Q1Real.lean`, `AxialContour.lean`,
`FaithfulDeltaKNonScalar.lean` — every ingredient is imported and reused (LAW-19).
-/

namespace AdalyFormal.Balaban.NonDegenerateInstances

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessEll Bond witnessY)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AxialContour (Ax)
open AdalyFormal.Balaban.Q1Real (Q1Real q1RealKernel)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKUnified

/-! ## §1 — the two cardinalities and `0 < dim 𝔰𝔲(2)`, all computed rather than assumed -/

/-- `𝔰𝔲(2)` is nontrivial — `suTwoWitness ≠ 0`, already on record. Kept a `theorem` (not a global
`instance`) so this leaf module cannot perturb instance search anywhere else. -/
theorem suTwo_nontrivial : Nontrivial SuTwo := ⟨⟨suTwoWitness, 0, suTwoWitness_ne_zero⟩⟩

/-- **`0 < dim_ℝ 𝔰𝔲(2)`.** The exact value (`3`) is deliberately NOT used anywhere below: every
bound in this file is stated in terms of `Module.finrank ℝ SuTwo` and holds for whatever it is, so no
statement here depends on a basis computation that this file does not perform. -/
theorem finrank_suTwo_pos : 0 < Module.finrank ℝ SuTwo := by
  haveI := suTwo_nontrivial
  exact Module.finrank_pos

/-- **`#(fine bonds) = 192`** on the witness lattice (`witnessL = fun _ => 3`, side length `4`, so
`4³ · 3`). By `decide` — computed, not asserted. -/
theorem card_bond : Fintype.card (Bond witnessL) = 192 := by decide

/-- **`#(coarse bonds) = 24`** at `ell = witnessEll = 2` (`CoarseLattice` = sites with every
coordinate `≡ 0 mod 2`, i.e. `2³ = 8` sites, times `3` directions). By `decide`. -/
theorem card_coarseBond : Fintype.card (CoarseBond witnessL witnessEll) = 24 := by decide

#print axioms suTwo_nontrivial
#print axioms finrank_suTwo_pos
#print axioms card_bond
#print axioms card_coarseBond

/-! ## §2 — the three `(3.156)` clauses as ONE linear map, and `subspace156G` as its kernel

`DeltaKUnified.subspace156G` is `LambdaComplementLocusG Λ ⊓ AxUnionLocusG S' ell ⊓ q1RealKernel U`.
Each of the first two is a "vanish on a bond set" locus, hence the kernel of a restriction map; the
third is a kernel by definition. `LinearMap.prod` assembles the three into one map whose kernel is
the intersection (`LinearMap.ker_prod`), which is what makes rank–nullity available. -/

/-- Restriction of a fine-bond field to a `Finset` of bonds, as a genuine `LinearMap`. -/
def restrictBonds (T : Finset (Bond witnessL)) :
    (Bond witnessL → SuTwo) →ₗ[ℝ] ({b : Bond witnessL // b ∈ T} → SuTwo) where
  toFun A := fun b => A b.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mem_ker_restrictBonds {T : Finset (Bond witnessL)} {A : Bond witnessL → SuTwo} :
    A ∈ LinearMap.ker (restrictBonds T) ↔ ∀ b ∈ T, A b = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h b hb
    exact congrFun h ⟨b, hb⟩
  · intro h
    funext b
    exact h b.1 b.2

/-- The bonds clause 1 forces to vanish: those BASED at a site outside `Λ`. Matches
`LambdaComplementLocusG`'s membership condition `∀ b, b.1 ∉ Λ → B b = 0` exactly (proved next, not
glossed — §QUOTE). -/
def outsideBonds (Lambda : Finset (PeriodicLatticeSite witnessL)) : Finset (Bond witnessL) :=
  Finset.univ.filter (fun b => b.1 ∉ Lambda)

theorem mem_outsideBonds {Lambda : Finset (PeriodicLatticeSite witnessL)} {b : Bond witnessL} :
    b ∈ outsideBonds Lambda ↔ b.1 ∉ Lambda := by
  simp [outsideBonds]

/-- The bonds clause 2 forces to vanish: `⋃_{y ∈ S'} Ax(y, ell)`, `AxialContour.Ax` REUSED. -/
def axBonds (S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) : Finset (Bond witnessL) :=
  S'.biUnion (fun y => Ax y ell)

theorem mem_axBonds {S' : Finset (PeriodicLatticeSite witnessL)} {ell : ℕ} {b : Bond witnessL} :
    b ∈ axBonds S' ell ↔ ∃ y ∈ S', b ∈ Ax y ell := by
  simp [axBonds]

theorem lambdaLocus_eq_ker (Lambda : Finset (PeriodicLatticeSite witnessL)) :
    LambdaComplementLocusG Lambda = LinearMap.ker (restrictBonds (outsideBonds Lambda)) := by
  ext A
  rw [mem_LambdaComplementLocusG, mem_ker_restrictBonds]
  constructor
  · intro h b hb; exact h b (mem_outsideBonds.mp hb)
  · intro h b hb; exact h b (mem_outsideBonds.mpr hb)

theorem axLocus_eq_ker (S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    AxUnionLocusG S' ell = LinearMap.ker (restrictBonds (axBonds S' ell)) := by
  ext A
  rw [mem_AxUnionLocusG, mem_ker_restrictBonds]
  constructor
  · intro h b hb
    obtain ⟨y, hy, hb'⟩ := mem_axBonds.mp hb
    exact h y hy b hb'
  · intro h y hy b hb
    exact h b (mem_axBonds.mpr ⟨y, hy, hb⟩)

#print axioms restrictBonds
#print axioms mem_ker_restrictBonds
#print axioms outsideBonds
#print axioms mem_outsideBonds
#print axioms axBonds
#print axioms mem_axBonds
#print axioms lambdaLocus_eq_ker
#print axioms axLocus_eq_ker

/-- The codomain of the assembled clause map. -/
abbrev ClauseCod (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) : Type :=
  ({b : Bond witnessL // b ∈ outsideBonds Lambda} → SuTwo) ×
    (({b : Bond witnessL // b ∈ axBonds S' ell} → SuTwo) ×
      (CoarseBond witnessL witnessEll → SuTwo))

/-- **THE THREE `(3.156)` CLAUSES AS ONE LINEAR MAP.** `Q1Real U` is the third component, so the
genuine, path-dependent, `U`-parameterized operator is carried unchanged; nothing about `U` is used
or assumed. -/
noncomputable def clauseMap (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (Bond witnessL → SuTwo) →ₗ[ℝ] ClauseCod Lambda S' ell :=
  (restrictBonds (outsideBonds Lambda)).prod
    ((restrictBonds (axBonds S' ell)).prod (Q1Real U))

/-- **`ker (clauseMap) = subspace156G`** — the assembly is faithful to `DeltaKUnified`'s own
definition, proved rather than arranged. -/
theorem ker_clauseMap (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (clauseMap Lambda S' ell U) = subspace156G Lambda S' ell U := by
  unfold clauseMap subspace156G
  rw [LinearMap.ker_prod, LinearMap.ker_prod, ← lambdaLocus_eq_ker, ← axLocus_eq_ker]
  exact (inf_assoc _ _ _).symm

/-- The same map on the `BFL2` carrier, precomposed with `bfl2Equiv`. -/
noncomputable def clauseMapBFL2 (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →ₗ[ℝ] ClauseCod Lambda S' ell :=
  clauseMap Lambda S' ell U ∘ₗ (bfl2Equiv (Lat := witnessL)).toLinearMap

/-- **`ker (clauseMapBFL2) = subspace156BFL2`** — `LinearMap.ker_comp` is literally the `comap`
`DeltaKUnified.subspace156BFL2` is defined by, so this is an identification, not a re-definition. -/
theorem ker_clauseMapBFL2 (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (clauseMapBFL2 Lambda S' ell U) = subspace156BFL2 Lambda S' ell U := by
  unfold clauseMapBFL2 subspace156BFL2
  rw [LinearMap.ker_comp, ker_clauseMap]

#print axioms clauseMap
#print axioms ker_clauseMap
#print axioms clauseMapBFL2
#print axioms ker_clauseMapBFL2

/-! ## §3 — the dimensions of domain and codomain -/

theorem finrank_bondFn :
    Module.finrank ℝ (Bond witnessL → SuTwo) = 192 * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_pi_fintype (R := ℝ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_bond]

/-- `BFL2 witnessL` has the same dimension — via the genuine `LinearEquiv` `bfl2Equiv`. -/
theorem finrank_bfl2 : Module.finrank ℝ (BFL2 witnessL) = 192 * Module.finrank ℝ SuTwo := by
  rw [(bfl2Equiv (Lat := witnessL)).finrank_eq, finrank_bondFn]

theorem finrank_clauseCod (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    Module.finrank ℝ (ClauseCod Lambda S' ell) =
      ((outsideBonds Lambda).card + (axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype (R := ℝ),
    Module.finrank_pi_fintype (R := ℝ), Module.finrank_pi_fintype (R := ℝ)]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe, card_coarseBond]
  ring

#print axioms finrank_bondFn
#print axioms finrank_bfl2
#print axioms finrank_clauseCod

/-- **THE RANK–NULLITY BOUND, in subtraction-free form.** `dim(domain) ≤ dim(codomain) + dim(ker)`,
with both dimensions computed above. No hypothesis on `Λ`, `S'`, `ell` or `U`. -/
theorem finrank_subspace156BFL2_lower (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo ≤
      ((outsideBonds Lambda).card + (axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo
        + Module.finrank ℝ (subspace156BFL2 Lambda S' ell U) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (clauseMapBFL2 Lambda S' ell U)
  rw [ker_clauseMapBFL2, finrank_bfl2] at hrn
  have hle : Module.finrank ℝ (LinearMap.range (clauseMapBFL2 Lambda S' ell U)) ≤
      Module.finrank ℝ (ClauseCod Lambda S' ell) := Submodule.finrank_le _
  rw [finrank_clauseCod] at hle
  omega

#print axioms finrank_subspace156BFL2_lower

/-! ### §3b — the cardinality hypothesis is the ONLY thing separating this from a FALSE statement

`DeltaKUnified.subspace156BFL2_eq_bot_of_lambda_empty` proves the subspace is `⊥` (hence dimension
`0`) at `Λ := ∅`. A dimension bound that fired there would be refuted by an existing theorem of this
tree. It does not fire: the hypothesis of §4 is FALSE at `Λ := ∅`, by `decide`. This is the
must-not-fire control (§CONTROL), watched rather than asserted. -/

theorem card_outsideBonds_empty : (outsideBonds (∅ : Finset (PeriodicLatticeSite witnessL))).card
    = 192 := by decide

theorem cardHyp_fails_at_lambda_empty (ell : ℕ) :
    ¬ ((outsideBonds (∅ : Finset (PeriodicLatticeSite witnessL))).card
        + (axBonds ∅ ell).card + 26 ≤ 192) := by
  rw [card_outsideBonds_empty]
  simp [axBonds]

#print axioms card_outsideBonds_empty
#print axioms cardHyp_fails_at_lambda_empty

/-! ### §3c — S82 GARBAGE SUBSTITUTION, made a THEOREM instead of prose

The bound above uses NO property of `Q1Real U` beyond its CODOMAIN. That is a real feature of the
argument and it is stated here as a theorem rather than left for a reader to notice: the same bound
holds with `Q1Real U` replaced by an ARBITRARY linear map `g` into the same codomain
(`finrank_ker_clauseMapGen_lower`), and at the garbage value `g := 0` the kernel is literally the
first two clauses (`ker_clauseMapGen_zero_eq`), where the bound is true and says nothing about any
coarse-graining operator at all.

**What that does and does not license.** It means the mathematical content of §4 is the CORANK COUNT
`24 · dim 𝔰𝔲(2)` against `192 · dim 𝔰𝔲(2)` — i.e. the fact that block-averaging to `ell = 2` coarse
bonds throws away a factor `8` of the degrees of freedom — and NOT any structural property of
Bałaban's `Q₀`. That count IS a genuine property of the coarse geometry, and it is exactly why the
conclusion is `U`-uniform: `U` enters `Q1Real` only inside the transports, which cannot change the
codomain. It is also why §4 must NOT be read as evidence that the admissible subspace is large *for
the reasons Bałaban's construction needs* — only that it is large. -/

/-- The clause map with an ARBITRARY third component. -/
noncomputable def clauseMapGen (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (g : (Bond witnessL → SuTwo) →ₗ[ℝ] (CoarseBond witnessL witnessEll → SuTwo)) :
    (Bond witnessL → SuTwo) →ₗ[ℝ] ClauseCod Lambda S' ell :=
  (restrictBonds (outsideBonds Lambda)).prod
    ((restrictBonds (axBonds S' ell)).prod g)

theorem clauseMap_eq_gen (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    clauseMap Lambda S' ell U = clauseMapGen Lambda S' ell (Q1Real U) := rfl

/-- **The corank bound, for an ARBITRARY third clause** — the S82 disclosure as a theorem. -/
theorem finrank_ker_clauseMapGen_lower (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (g : (Bond witnessL → SuTwo) →ₗ[ℝ] (CoarseBond witnessL witnessEll → SuTwo)) :
    192 * Module.finrank ℝ SuTwo ≤
      ((outsideBonds Lambda).card + (axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo
        + Module.finrank ℝ (LinearMap.ker (clauseMapGen Lambda S' ell g)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (clauseMapGen Lambda S' ell g)
  rw [finrank_bondFn] at hrn
  have hle : Module.finrank ℝ (LinearMap.range (clauseMapGen Lambda S' ell g)) ≤
      Module.finrank ℝ (ClauseCod Lambda S' ell) := Submodule.finrank_le _
  rw [finrank_clauseCod] at hle
  omega

/-- **At the garbage value `g := 0` the kernel is just the two locus clauses** — so the bound of
`finrank_ker_clauseMapGen_lower` is satisfied by a map with no coarse-graining content whatsoever.
Exhibited, not asserted. -/
theorem ker_clauseMapGen_zero_eq (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    LinearMap.ker (clauseMapGen Lambda S' ell 0) =
      LambdaComplementLocusG Lambda ⊓ AxUnionLocusG S' ell := by
  unfold clauseMapGen
  rw [LinearMap.ker_prod, LinearMap.ker_prod, ← lambdaLocus_eq_ker, ← axLocus_eq_ker,
    LinearMap.ker_zero, inf_top_eq]

/-- The bare-carrier form of §3's bound (the `BFL2` version is `finrank_subspace156BFL2_lower`);
`subspace156G` is where the curl operator of §7 acts. -/
theorem finrank_subspace156G_lower (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo ≤
      ((outsideBonds Lambda).card + (axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo
        + Module.finrank ℝ (subspace156G Lambda S' ell U) := by
  have h := finrank_ker_clauseMapGen_lower Lambda S' ell (Q1Real U)
  rw [← clauseMap_eq_gen, ker_clauseMap] at h
  exact h

#print axioms ClauseCod
#print axioms clauseMapGen
#print axioms clauseMap_eq_gen
#print axioms finrank_ker_clauseMapGen_lower
#print axioms ker_clauseMapGen_zero_eq
#print axioms finrank_subspace156G_lower

/-! ## §4 — **THE DELIVERABLE**: `2 ≤ dim V`, for EVERY `U` -/

/-- **`2 ≤ dim_ℝ (subspace156BFL2 Λ S' ell U)` for EVERY `U`**, under the cardinality hypothesis
alone. No flatness, no regularity, no witness. This is the statement
`FaithfulDeltaKNonScalar.lean` named as the missing prerequisite for a non-scalarity conjunct on
`V` (*"on a 1-dimensional space EVERY operator is trivially scalar"*). -/
theorem two_le_finrank_subspace156BFL2 (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcard : (outsideBonds Lambda).card + (axBonds S' ell).card + 26 ≤ 192) :
    2 ≤ Module.finrank ℝ (subspace156BFL2 Lambda S' ell U) := by
  have hs := finrank_suTwo_pos
  have hlow := finrank_subspace156BFL2_lower Lambda S' ell U
  set s := Module.finrank ℝ SuTwo with hsdef
  set n := (outsideBonds Lambda).card + (axBonds S' ell).card + 24 with hndef
  set F := Module.finrank ℝ (subspace156BFL2 Lambda S' ell U) with hFdef
  have hn2 : n + 2 ≤ 192 := by omega
  have hmul : (n + 2) * s ≤ 192 * s := Nat.mul_le_mul_right s hn2
  have hexp : (n + 2) * s = n * s + 2 * s := by ring
  have h1 : n * s + 2 * s ≤ n * s + F := by
    calc n * s + 2 * s = (n + 2) * s := hexp.symm
      _ ≤ 192 * s := hmul
      _ ≤ n * s + F := hlow
  have h2 : 2 * s ≤ F := Nat.le_of_add_le_add_left h1
  omega

#print axioms two_le_finrank_subspace156BFL2

/-- **The `Λ := univ`, `S' := ∅` specialization, with the FULL deficit: `168 · dim 𝔰𝔲(2) ≤ dim V`,
at EVERY `U`.** Both locus clauses are `⊤` here (`outsideBonds univ = ∅`, `axBonds ∅ ell = ∅`), so
the whole bound is the corank of `Q1Real U`. -/
theorem finrank_subspace156BFL2_univ_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    168 * Module.finrank ℝ SuTwo ≤
      Module.finrank ℝ (subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL))
        ∅ ell U) := by
  have hlow := finrank_subspace156BFL2_lower
    (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U
  have h1 : (outsideBonds (Finset.univ : Finset (PeriodicLatticeSite witnessL))).card = 0 := by
    simp [outsideBonds]
  have h2 : (axBonds (∅ : Finset (PeriodicLatticeSite witnessL)) ell).card = 0 := by
    simp [axBonds]
  rw [h1, h2] at hlow
  omega

/-- Corollary, `2 ≤ dim V` at `Λ := univ`, `S' := ∅`, EVERY `U`. -/
theorem two_le_finrank_subspace156BFL2_univ_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    2 ≤ Module.finrank ℝ (subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL))
      ∅ ell U) := by
  refine two_le_finrank_subspace156BFL2 _ _ ell U ?_
  have h1 : (outsideBonds (Finset.univ : Finset (PeriodicLatticeSite witnessL))).card = 0 := by
    simp [outsideBonds]
  have h2 : (axBonds (∅ : Finset (PeriodicLatticeSite witnessL)) ell).card = 0 := by
    simp [axBonds]
  rw [h1, h2]
  omega

/-- **`subspace156BFL2 ≠ ⊥` at EVERY `U`** — the `"only at trivialU"` caveat on
`DeltaKUnified.subspace156BFL2_ne_bot` lifted, by a route that never touches
`checkerConfigSuTwo` and so never inherits its flat-background restriction. -/
theorem subspace156BFL2_ne_bot_of_card (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcard : (outsideBonds Lambda).card + (axBonds S' ell).card + 26 ≤ 192) :
    subspace156BFL2 Lambda S' ell U ≠ ⊥ := by
  intro hbot
  have h := two_le_finrank_subspace156BFL2 Lambda S' ell U hcard
  rw [hbot, finrank_bot] at h
  omega

theorem subspace156BFL2_ne_bot_univ_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U ≠ ⊥ := by
  intro hbot
  have h := two_le_finrank_subspace156BFL2_univ_empty ell U
  rw [hbot, finrank_bot] at h
  omega

#print axioms finrank_subspace156BFL2_univ_empty
#print axioms two_le_finrank_subspace156BFL2_univ_empty
#print axioms subspace156BFL2_ne_bot_of_card
#print axioms subspace156BFL2_ne_bot_univ_empty

/-! ## §5 — the NON-DEGENERATE parameter point: `Λ` PROPER, `S'` NONEMPTY, `U` ARBITRARY

`DeltaKUnified.lean` §5 residual 3 records as open: *"`subspace156BFL2 ≠ ⊥` at a non-trivial
`S'`/proper `Λ` — open (§3's closing note); the proved witness uses `S' = ∅`, `Λ = Finset.univ`,
both forced/convenient degeneracies of the SPECIFIC witness `checkerConfigSuTwo`"*; residual 4
records the `trivialU` restriction. Both are closed here at once, because the route uses no witness:
at `Λ := univ.erase witnessY`, `S' := {witnessY}`, `ell := witnessEll = 2` the two locus
cardinalities are `3` and `7` (`decide`), so `3 + 7 + 26 = 36 ≤ 192`. -/

theorem card_outsideBonds_erase_witnessY :
    (outsideBonds (Finset.univ.erase witnessY)).card = 3 := by decide

theorem card_axBonds_singleton_witnessY :
    (axBonds {witnessY} witnessEll).card = 7 := by decide

/-- **THE NON-DEGENERATE INSTANCE: `158 · dim 𝔰𝔲(2) ≤ dim V` at a PROPER `Λ`, a NONEMPTY `S'`, and
EVERY `U`** — in particular at the tree's own non-flat `CovariantOperators.witnessU`.

⚠ **NOT SHARP (S75, §8):** the `3 + 7` charge double-counts — all three `Λ`-forbidden bonds are
axial here (`outsideBonds_subset_axBonds_nondegenerate`, `decide`), so the union charges `7` and the
sharp bound is `161 · dim 𝔰𝔲(2)` (`finrank_subspace156G_nondegenerate_sharp`). This statement is
TRUE and is retained; consumers wanting the extra `3` should use the §8 one. -/
theorem finrank_subspace156BFL2_nondegenerate
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    158 * Module.finrank ℝ SuTwo ≤
      Module.finrank ℝ (subspace156BFL2 (Finset.univ.erase witnessY) {witnessY} witnessEll U) := by
  have hlow := finrank_subspace156BFL2_lower (Finset.univ.erase witnessY) {witnessY} witnessEll U
  rw [card_outsideBonds_erase_witnessY, card_axBonds_singleton_witnessY] at hlow
  omega

theorem two_le_finrank_subspace156BFL2_nondegenerate
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    2 ≤ Module.finrank ℝ
      (subspace156BFL2 (Finset.univ.erase witnessY) {witnessY} witnessEll U) := by
  refine two_le_finrank_subspace156BFL2 _ _ witnessEll U ?_
  rw [card_outsideBonds_erase_witnessY, card_axBonds_singleton_witnessY]
  omega

theorem subspace156BFL2_ne_bot_nondegenerate
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    subspace156BFL2 (Finset.univ.erase witnessY) {witnessY} witnessEll U ≠ ⊥ := by
  refine subspace156BFL2_ne_bot_of_card _ _ witnessEll U ?_
  rw [card_outsideBonds_erase_witnessY, card_axBonds_singleton_witnessY]
  omega

/-- **`Λ := univ.erase witnessY` really is PROPER and `S' := {witnessY}` really is NONEMPTY** — the
non-degeneracy of the parameter point itself, checked rather than claimed. -/
theorem nondegenerate_params_are_nondegenerate :
    (Finset.univ.erase witnessY) ≠ (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∧
      ({witnessY} : Finset (PeriodicLatticeSite witnessL)) ≠ ∅ := by
  refine ⟨?_, ?_⟩
  · intro h
    have : witnessY ∈ Finset.univ.erase witnessY := by rw [h]; exact Finset.mem_univ _
    exact (Finset.notMem_erase witnessY Finset.univ) this
  · exact Finset.singleton_ne_empty witnessY

#print axioms card_outsideBonds_erase_witnessY
#print axioms card_axBonds_singleton_witnessY
#print axioms finrank_subspace156BFL2_nondegenerate
#print axioms two_le_finrank_subspace156BFL2_nondegenerate
#print axioms subspace156BFL2_ne_bot_nondegenerate
#print axioms nondegenerate_params_are_nondegenerate

/-! ### §5b — the `ell ∈ {0,1}` degenerate points, recorded (§DEGEN)

Clause 2 is VACUOUS at `ell ∈ {0,1}`: `Ax y ell = (blockOf y ell).erase y |>.biUnion …` and at
`ell = 0` the block is empty while at `ell = 1` it is `{y}`, so the erase empties it. Recorded so
that no reader of §5 treats a small-`ell` instance as evidence that clause 2 constrains anything. -/

theorem ax_witnessY_zero : Ax witnessY 0 = ∅ := by decide
theorem ax_witnessY_one : Ax witnessY 1 = ∅ := by decide

#print axioms ax_witnessY_zero
#print axioms ax_witnessY_one

/-! ## §6 — NAMED MEMBERS: three directional checkerboards, and `2 ≤ dim V` a SECOND, INDEPENDENT WAY

§4 delivers dimension without vectors. A downstream non-scalarity argument consumes VECTORS, so this
section also builds them, and in doing so gives a completely independent derivation of `2 ≤ dim V` —
one that shares no lemma with §2–§4 (no `clauseMap`, no rank–nullity, no cardinality `decide`), so an
error in §2's assembly could not produce both. `Q1Real.checkerConfigSuTwo`'s proof is generalized from
its hard-wired direction `0` to an arbitrary direction `μ` (`checkerDirSuTwo`, and
`checkerDirSuTwo_zero_eq` records that `μ = 0` recovers the original object verbatim, so this is a
generalization and not a second copy).

**Scope, stated at its true strength**: like the object it generalizes, kernel membership is proved
ONLY at `trivialU` — the pointwise cancellation is a flat-background phenomenon
(`Q1Real.lean` §9's own disclosure, unchanged). §4's `U`-uniform bound does not depend on anything
here, and nothing here is evidence at non-flat `U`. -/

open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_trivialU q1RealMain checkerConfigSuTwo)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf)
open AdalyFormal.Target.ClayStatement (periodicLatticeShift)

/-- **The direction-`μ` checkerboard alternator.** `Q1Real.checkerConfigSuTwo` is exactly the `μ = 0`
member (`checkerDirSuTwo_zero_eq`), so this is a generalization of that object, not a duplicate of it
(LAW-19 / §GREEN item 10: one text only). -/
noncomputable def checkerDirSuTwo (μ : Fin 3) : Bond witnessL → SuTwo :=
  fun e => if e.2 = μ then ((-1 : ℝ) ^ (e.1 μ).val) • suTwoWitness else 0

theorem checkerDirSuTwo_zero_eq : checkerDirSuTwo 0 = checkerConfigSuTwo := rfl

/-- The pointwise cancellation, now for every direction: consecutive sites along `μ` carry opposite
signs, and `witnessL`'s side length `4` is even so the periodic identification is consistent. -/
theorem checkerDirSuTwo_pointwise_cancel (μ : Fin 3) (x : PeriodicLatticeSite witnessL) :
    checkerDirSuTwo μ (x, μ) + checkerDirSuTwo μ (periodicLatticeShift x μ, μ) = 0 := by
  have hshift : (periodicLatticeShift x μ) μ = x μ + 1 := by
    simp [periodicLatticeShift, Function.update_self]
  have h1 : checkerDirSuTwo μ (x, μ) = ((-1 : ℝ) ^ (x μ).val) • suTwoWitness := by
    simp [checkerDirSuTwo]
  have h2 : checkerDirSuTwo μ (periodicLatticeShift x μ, μ) =
      ((-1 : ℝ) ^ ((periodicLatticeShift x μ) μ).val) • suTwoWitness := by
    simp [checkerDirSuTwo]
  rw [h1, h2, hshift, ← add_smul]
  generalize hv : x μ = v
  have hz : ((-1 : ℝ) ^ v.val + (-1 : ℝ) ^ (v + 1).val) = 0 := by
    fin_cases v <;> norm_num [Fin.add_def, witnessL]
  rw [hz, zero_smul]

/-- **`checkerDirSuTwo μ ∈ ker Q₁(1)` for every direction `μ`** — the direction-`μ` generalization of
`Q1Real.checkerConfigSuTwo_mem_q1RealKernel_trivialU`, same mechanism, same `trivialU` scope. -/
theorem checkerDirSuTwo_mem_q1RealKernel_trivialU (μ : Fin 3) :
    checkerDirSuTwo μ ∈ q1RealKernel (trivialU witnessL) := by
  rw [q1RealKernel, LinearMap.mem_ker, Q1Real, LinearMap.coe_mk, AddHom.coe_mk]
  funext b
  show q1RealMain (trivialU witnessL) witnessEll (checkerDirSuTwo μ) b = 0
  unfold q1RealMain
  rcases eq_or_ne b.2 μ with hmu | hmu
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        rZeroA (trivialU witnessL) b.1.1 x (checkerDirSuTwo μ) b.2 witnessEll = 0 := by
      intro x _
      rw [hmu, rZeroA_trivialU]
      show ∑ i ∈ Finset.range 2, checkerDirSuTwo μ (pathSite x μ i, μ) = 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pathSite_zero,
        pathSite_succ]
      exact checkerDirSuTwo_pointwise_cancel μ x
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        rZeroA (trivialU witnessL) b.1.1 x (checkerDirSuTwo μ) b.2 witnessEll = 0 := by
      intro x _
      rw [rZeroA_trivialU]
      apply Finset.sum_eq_zero
      intro i _
      simp only [checkerDirSuTwo]
      rw [if_neg hmu]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]

/-- The value at the bond `(witnessY, μ)` is `suTwoWitness` — the point at which independence is
tested below. `witnessY = fun _ => 0`, so the sign is `(-1)^0 = 1`. -/
theorem checkerDirSuTwo_at_witnessY (μ : Fin 3) :
    checkerDirSuTwo μ (witnessY, μ) = suTwoWitness := by
  simp [checkerDirSuTwo, witnessY, AdalyFormal.Balaban.AdmissibleSubspace.witnessY]

/-- The value at a bond of a DIFFERENT direction is `0` — the disjoint-support fact making distinct
directions independent. -/
theorem checkerDirSuTwo_off_direction (μ ν : Fin 3) (h : ν ≠ μ)
    (x : PeriodicLatticeSite witnessL) : checkerDirSuTwo μ (x, ν) = 0 := by
  simp only [checkerDirSuTwo]
  rw [if_neg h]

/-- The named members on the `BFL2` carrier. -/
noncomputable def checkerDirBFL2 (μ : Fin 3) : BFL2 witnessL :=
  (bfl2Equiv (Lat := witnessL)).symm (checkerDirSuTwo μ)

theorem checkerDirBFL2_mem (μ : Fin 3) (ell : ℕ) :
    checkerDirBFL2 μ ∈ subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell
      (trivialU witnessL) := by
  show checkerDirSuTwo μ ∈ subspace156G Finset.univ ∅ ell (trivialU witnessL)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro b hb; exact absurd (Finset.mem_univ b.1) hb
  · intro y hy; exact absurd hy (Finset.notMem_empty y)
  · exact checkerDirSuTwo_mem_q1RealKernel_trivialU μ

#print axioms checkerDirSuTwo
#print axioms checkerDirSuTwo_zero_eq
#print axioms checkerDirSuTwo_pointwise_cancel
#print axioms checkerDirSuTwo_mem_q1RealKernel_trivialU
#print axioms checkerDirSuTwo_at_witnessY
#print axioms checkerDirSuTwo_off_direction
#print axioms checkerDirBFL2
#print axioms checkerDirBFL2_mem

/-- **The direction-`0` and direction-`1` members are LINEARLY INDEPENDENT** — disjoint supports,
tested at the two bonds `(witnessY, 0)` and `(witnessY, 1)`. -/
theorem checkerDir_linearIndependent :
    LinearIndependent ℝ (![checkerDirBFL2 0, checkerDirBFL2 1]) := by
  rw [linearIndependent_fin2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    intro hz
    have hc := congrArg (bfl2Equiv (Lat := witnessL)) hz
    rw [map_zero] at hc
    show False
    have hval : checkerDirSuTwo 1 (witnessY, (1 : Fin 3)) = 0 := by
      have := congrFun hc (witnessY, (1 : Fin 3))
      simpa [checkerDirBFL2] using this
    rw [checkerDirSuTwo_at_witnessY] at hval
    exact suTwoWitness_ne_zero hval
  · intro a hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    have hc := congrArg (bfl2Equiv (Lat := witnessL)) hz
    have hval := congrFun hc (witnessY, (0 : Fin 3))
    simp only [checkerDirBFL2, LinearEquiv.apply_symm_apply, map_smul, Pi.smul_apply] at hval
    rw [checkerDirSuTwo_at_witnessY,
      checkerDirSuTwo_off_direction 1 0 (by decide) witnessY, smul_zero] at hval
    exact suTwoWitness_ne_zero hval.symm

/-- **`2 ≤ dim V` at `trivialU`, DERIVED FROM THE EXPLICIT MEMBERS** — an independent second route to
§4's conclusion at the flat background, sharing no lemma with §2–§4. -/
theorem two_le_finrank_subspace156BFL2_explicit (ell : ℕ) :
    2 ≤ Module.finrank ℝ (subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      ell (trivialU witnessL)) := by
  have hli := checkerDir_linearIndependent
  have hspan : Submodule.span ℝ (Set.range (![checkerDirBFL2 0, checkerDirBFL2 1])) ≤
      subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell
        (trivialU witnessL) := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    fin_cases i
    · exact checkerDirBFL2_mem 0 ell
    · exact checkerDirBFL2_mem 1 ell
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (![checkerDirBFL2 0, checkerDirBFL2 1]))) = 2 := by
    rw [finrank_span_eq_card hli]; simp
  calc (2 : ℕ) = Module.finrank ℝ
        (Submodule.span ℝ (Set.range (![checkerDirBFL2 0, checkerDirBFL2 1]))) := hcard.symm
    _ ≤ _ := Submodule.finrank_mono hspan

#print axioms checkerDir_linearIndependent
#print axioms two_le_finrank_subspace156BFL2_explicit


/-! ## §7 — WHAT `dim V ≥ 2` UNLOCKS: the curl operator is NOT SCALAR on the admissible subspace

`FaithfulDeltaKNonScalar.lean`'s "WHAT THIS FILE DOES NOT CLOSE" item 1 names TWO missing pieces for
a non-scalarity statement ON `V`: (a) `dim V ≥ 2`, and (b) witnesses that are SIMULTANEOUSLY
admissible (`∈ q1RealKernel U`) and distinguish the operator's action — *"the natural curl witnesses,
`constDirConfig`/`bondWitnessConfig`, are not shown, and are not expected in general, to lie in
`q1RealKernel`"*. §4 supplies (a). This section supplies (b) and then splits the non-scalarity
statement into two halves, each proved at its own true scope:

* **Every NONZERO scalar is killed, for EVERY `U`, with no witness at all** (§7b,
  `bondLaplacianCov_not_nonzero_scalar_on_subspace156G`). Pure dimension: if
  `D_U D_U^* = c·id` on `V` with `c ≠ 0` then `V ∩ ker(D_U D_U^*) = 0`, so
  `dim V + dim ker(D_U D_U^*) ≤ 192·dim 𝔰𝔲(2)`; but `ker D_U^* ⊆ ker(D_U D_U^*)` and rank–nullity on
  `D_U^* : (Bond → 𝔰𝔲(2)) → (Site → 𝔰𝔲(2))` forces `dim ker D_U^* ≥ (192−64)·dim 𝔰𝔲(2)`, and
  `128 + 168 > 192`. The contradiction is arithmetic and uniform in `U`.
* **The scalar `0` is killed at `trivialU`, by an EXPLICIT admissible witness** (§7c,
  `bondLaplacianCov_not_scalar_on_subspace156G_trivialU`, which kills every `c` at once).
  `signDir01SuTwo` — the direction-`0` field with sign `(−1)^{x₀+x₁}` — lies in `q1RealKernel 1` by
  the SAME pointwise cancellation as `checkerDirSuTwo` (the `x₁` factor is common to both addends),
  and `D_1 D_1^*` sends it to a field that is NONZERO on a direction-`1` bond where the field itself
  VANISHES (`bondLaplacian_signDir01_at_witnessY_dir1`: the value at `(witnessY, 1)` is
  `4 • suTwoWitness`, while `signDir01SuTwo (witnessY, 1) = 0`). So no multiple of it can be its
  image. This is exactly the missing piece (b): an admissible field that distinguishes the curl term.

**THE LAST CASE, `c = 0`.** ~~The one surviving case is `c = 0` at a NON-FLAT `U`~~ — see §7d, which
CLOSES it at `Λ := univ`, `S' := ∅` for every `U`. The reduction is exact and is worth stating
because §7d uses it: `c = 0` survives iff `V ⊆ ker(D_U D_U^*)`, so it dies as soon as
`dim ker(D_U D_U^*) < dim V`, for which it suffices that
`rank (gradCovariantAdjointLM U) > 24 · dim 𝔰𝔲(2)` TOGETHER WITH `ker (D_U D_U^*) = ker D_U^*`.

~~Both were attempted here and each has a concrete, identified stopping point:~~
~~1. `ker (D_U D_U^*) = ker D_U^*` needs DEFINITENESS of `covSiteInner`~~
~~   (`covSiteInner X X = 0 → X = 0`) … but `CovariantHjMinimizer.lean` proves only~~
~~   `covSiteInner_self_nonneg`, and `hsInner` has no `hsInner_self_eq_zero` anywhere in the tree~~
~~   (grepped). That is a small, self-contained missing lemma …~~

⚠ **THE STRUCK CLAIM WAS FALSE AND IS CORRECTED HERE IN THE SAME PASS (S75).** The grep behind it was
scoped to three files. `SuTwoInner.lean:148` proves exactly
`hsInner_self_eq_zero {X : SuTwo} (h : hsInner X X = 0) : X = 0`, and `CovU1Reduction.lean:180`
already consumes it. **The tree already held the fact** — so the case was never blocked, and §7d below
builds both steps and closes it:

1. `ker (D_U D_U^*) = ker D_U^*` — `ker_bondLaplacian_eq_ker_gradAdjoint`, from
   `BondSU2Space.covBondInner_bondLaplacianCovLM_eq_covSiteInner` plus `covSiteInner_self_eq_zero`
   (proved in §7d from the pre-existing `hsInner_self_eq_zero`, termwise).
2. `rank D_U^* ≥ 32 · dim 𝔰𝔲(2)` for EVERY `U` — `finrank_range_gradAdjoint_lower`, by the 32-bond
   even-`x₀` scatter described in §7d, which uses no property of `U`.

~~**What §7d still does NOT reach, with the exact arithmetic.** The §5 NON-DEGENERATE parameter point:
there `dim V ≥ 158 · dim 𝔰𝔲(2)` while the 32-bond scatter only gives
`dim ker D_U^* ≤ 160 · dim 𝔰𝔲(2)`, and `158 < 160`. That point needs
`rank D_U^* > 34 · dim 𝔰𝔲(2)`; the identified refinement is the 48 direction-`0` bonds with `x₀ ≤ 2`,
whose evaluation is LOWER-TRIANGULAR with `−id` on the diagonal, giving `48 · dim 𝔰𝔲(2)` and
`dim ker D_U^* ≤ 144 · dim 𝔰𝔲(2) < 158 · dim 𝔰𝔲(2)`. The triangular induction over the three layers
is the only extra content; it is not built here.~~

⚠ **SUPERSEDED BY §8 (S75).** Both halves of that paragraph are now discharged, and its premise was
not sharp: the `3 + 7` charge double-counts an overlap (`outsideBonds ⊆ axBonds` at this parameter
point, `decide`), so the real bound is `161 · dim 𝔰𝔲(2)` and beats `160` unaided. The 48-bond
triangular induction is built anyway (`adjScatterT_layer_ker_eq_bot`, at ARBITRARY transports), and
`bondLaplacianCov_not_scalar_nondegenerate` closes every `c` at this point for every `U`. -/

open AdalyFormal.Balaban.CovariantOperators (RMap RMap_one gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU gradCovariantAdjointValue
  gradCovariantAdjointLM periodicLatticeShiftBack)
open AdalyFormal.Balaban.BondSU2Space (bondLaplacianCovLM bondLaplacianCovLM_apply)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_trivialU q1RealMain)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf)
open AdalyFormal.Target.ClayStatement (periodicLatticeShift)

/-! ### §7a — the kernel of `D_U^*` is enormous, uniformly in `U` -/

theorem card_site : Fintype.card (PeriodicLatticeSite witnessL) = 64 := by decide

theorem finrank_siteFn :
    Module.finrank ℝ (PeriodicLatticeSite witnessL → SuTwo) = 64 * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_pi_fintype (R := ℝ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_site]

/-- **`dim ker D_U^* ≥ (192 − 64)·dim 𝔰𝔲(2)`, for EVERY `U`** — rank–nullity on the covariant
divergence, subtraction-free. -/
theorem finrank_ker_gradAdjoint_lower
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo ≤ 64 * Module.finrank ℝ SuTwo
      + Module.finrank ℝ (LinearMap.ker (gradCovariantAdjointLM U)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (gradCovariantAdjointLM U)
  rw [finrank_bondFn] at hrn
  have hle : Module.finrank ℝ (LinearMap.range (gradCovariantAdjointLM U)) ≤
      Module.finrank ℝ (PeriodicLatticeSite witnessL → SuTwo) := Submodule.finrank_le _
  rw [finrank_siteFn] at hle
  omega

/-- The same bound for `ker (D_U D_U^*)`, which CONTAINS `ker D_U^*` (`LinearMap.ker_le_ker_comp`,
`bondLaplacianCovLM = gradCovariantLM ∘ gradCovariantAdjointLM` by definition). -/
theorem finrank_ker_bondLaplacian_lower
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo ≤ 64 * Module.finrank ℝ SuTwo
      + Module.finrank ℝ (LinearMap.ker (bondLaplacianCovLM U)) := by
  have hsub : LinearMap.ker (gradCovariantAdjointLM U) ≤ LinearMap.ker (bondLaplacianCovLM U) :=
    LinearMap.ker_le_ker_comp _ _
  have hmono := Submodule.finrank_mono hsub
  have h := finrank_ker_gradAdjoint_lower U
  omega

#print axioms card_site
#print axioms finrank_siteFn
#print axioms finrank_ker_gradAdjoint_lower
#print axioms finrank_ker_bondLaplacian_lower

/-! ### §7b — EVERY NONZERO SCALAR is killed, for EVERY `U`, by dimension alone -/

/-- **`D_U D_U^*` is not `c · id` on the admissible subspace, for any `c ≠ 0` and EVERY `U`.** No
witness, no flatness, no regularity. The cardinality hypothesis (`… + 24 + 64 ≤ 191`) is exactly what
makes `dim V` too large to be disjoint from `ker (D_U D_U^*)`. -/
theorem bondLaplacianCov_not_nonzero_scalar_on_subspace156G
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcard : (outsideBonds Lambda).card + (axBonds S' ell).card + 24 + 64 ≤ 191)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = c • v) := by
  intro hscal
  have hs := finrank_suTwo_pos
  set s := Module.finrank ℝ SuTwo with hsdef
  set n := (outsideBonds Lambda).card + (axBonds S' ell).card + 24 with hndef
  -- (i) `V` and `ker (D_U D_U^*)` intersect trivially, because `c ≠ 0`.
  have hdisj : subspace156G Lambda S' ell U ⊓ LinearMap.ker (bondLaplacianCovLM U) = ⊥ := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hV, hK⟩ := hv
      have h1 : bondLaplacianCovLM U v = c • v := hscal v hV
      have h2 : bondLaplacianCovLM U v = 0 := LinearMap.mem_ker.mp hK
      have h3 : c • v = 0 := by rw [← h1, h2]
      rcases smul_eq_zero.mp h3 with h | h
      · exact absurd h hc
      · exact (Submodule.mem_bot ℝ).mpr h
    · exact bot_le
  -- (ii) so their dimensions add to at most the whole space.
  have hsum : Module.finrank ℝ (subspace156G Lambda S' ell U)
      + Module.finrank ℝ (LinearMap.ker (bondLaplacianCovLM U)) ≤ 192 * s := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq
      (subspace156G Lambda S' ell U) (LinearMap.ker (bondLaplacianCovLM U))
    rw [hdisj, finrank_bot] at he
    have hle : Module.finrank ℝ
        ((subspace156G Lambda S' ell U ⊔ LinearMap.ker (bondLaplacianCovLM U) :
          Submodule ℝ (Bond witnessL → SuTwo))) ≤
        Module.finrank ℝ (Bond witnessL → SuTwo) := Submodule.finrank_le _
    rw [finrank_bondFn] at hle
    omega
  -- (iii) but `ker (D_U D_U^*)` alone already occupies `128·s`, so `dim V ≤ 64·s`.
  have hker := finrank_ker_bondLaplacian_lower U
  have hV64 : Module.finrank ℝ (subspace156G Lambda S' ell U) ≤ 64 * s := by omega
  -- (iv) and `dim V ≥ (192 − n)·s` contradicts that once `n + 64 ≤ 191`.
  have hlow := finrank_subspace156G_lower Lambda S' ell U
  have hchain : 192 * s ≤ 191 * s := by
    calc 192 * s ≤ n * s + Module.finrank ℝ (subspace156G Lambda S' ell U) := hlow
      _ ≤ n * s + 64 * s := by omega
      _ = (n + 64) * s := by ring
      _ ≤ 191 * s := Nat.mul_le_mul_right s (by omega)
  omega

/-- Specialization at `Λ := univ`, `S' := ∅` (`n = 24`, `24 + 64 = 88 ≤ 191`): for EVERY `U`, no
nonzero scalar. -/
theorem bondLaplacianCov_not_nonzero_scalar_univ_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ v ∈ subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U,
        bondLaplacianCovLM U v = c • v) := by
  refine bondLaplacianCov_not_nonzero_scalar_on_subspace156G _ _ ell U ?_ c hc
  have h1 : (outsideBonds (Finset.univ : Finset (PeriodicLatticeSite witnessL))).card = 0 := by
    simp [outsideBonds]
  have h2 : (axBonds (∅ : Finset (PeriodicLatticeSite witnessL)) ell).card = 0 := by
    simp [axBonds]
  rw [h1, h2]
  omega

/-- Specialization at the §5 non-degenerate parameter point (`n = 34`, `34 + 64 = 98 ≤ 191`). -/
theorem bondLaplacianCov_not_nonzero_scalar_nondegenerate
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U,
        bondLaplacianCovLM U v = c • v) := by
  refine bondLaplacianCov_not_nonzero_scalar_on_subspace156G _ _ witnessEll U ?_ c hc
  rw [card_outsideBonds_erase_witnessY, card_axBonds_singleton_witnessY]
  omega

#print axioms bondLaplacianCov_not_nonzero_scalar_on_subspace156G
#print axioms bondLaplacianCov_not_nonzero_scalar_univ_empty
#print axioms bondLaplacianCov_not_nonzero_scalar_nondegenerate

/-! ### §7c — an ADMISSIBLE witness that distinguishes the curl term, at `trivialU`

The missing piece (b) of `FaithfulDeltaKNonScalar.lean` item 1. -/

/-- **`signDir01SuTwo`**: the direction-`0` field with sign `(−1)^{x₀+x₁}`. The `x₁` factor is
COMMON to the two addends of the direction-`0` cancellation, so admissibility survives it; but it
makes the covariant divergence depend on `x₁`, which is what breaks the eigenvector property that
`checkerDirSuTwo 0` has. -/
noncomputable def signDir01SuTwo : Bond witnessL → SuTwo :=
  fun e => if e.2 = (0 : Fin 3) then
    ((-1 : ℝ) ^ ((e.1 0).val + (e.1 1).val)) • suTwoWitness else 0

theorem signDir01_dir0 (x : PeriodicLatticeSite witnessL) :
    signDir01SuTwo (x, (0 : Fin 3))
      = ((-1 : ℝ) ^ ((x 0).val + (x 1).val)) • suTwoWitness := by simp [signDir01SuTwo]

theorem signDir01_pointwise_cancel (x : PeriodicLatticeSite witnessL) :
    signDir01SuTwo (x, (0 : Fin 3))
      + signDir01SuTwo (periodicLatticeShift x 0, (0 : Fin 3)) = 0 := by
  have hs0 : (periodicLatticeShift x 0) 0 = x 0 + 1 := by
    simp [periodicLatticeShift, Function.update_self]
  have hs1 : (periodicLatticeShift x 0) 1 = x 1 := by
    simp [periodicLatticeShift]
  rw [signDir01_dir0, signDir01_dir0, hs0, hs1, ← add_smul]
  have hz : ((-1 : ℝ) ^ ((x 0).val + (x 1).val)
      + (-1 : ℝ) ^ ((x 0 + 1).val + (x 1).val)) = 0 := by
    rw [pow_add, pow_add]
    have hv : ((-1 : ℝ)) ^ (x 0).val + ((-1 : ℝ)) ^ ((x 0) + 1).val = 0 := by
      generalize hh : x 0 = v
      fin_cases v <;> norm_num [Fin.add_def, witnessL]
    linear_combination ((-1 : ℝ) ^ (x 1).val) * hv
  rw [hz, zero_smul]

theorem signDir01_mem_kernel : signDir01SuTwo ∈ q1RealKernel (trivialU witnessL) := by
  rw [q1RealKernel, LinearMap.mem_ker, Q1Real, LinearMap.coe_mk, AddHom.coe_mk]
  funext b
  show q1RealMain (trivialU witnessL) witnessEll signDir01SuTwo b = 0
  unfold q1RealMain
  rcases eq_or_ne b.2 (0 : Fin 3) with hmu | hmu
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        rZeroA (trivialU witnessL) b.1.1 x signDir01SuTwo b.2 witnessEll = 0 := by
      intro x _
      rw [hmu, rZeroA_trivialU]
      show ∑ i ∈ Finset.range 2, signDir01SuTwo (pathSite x 0 i, (0 : Fin 3)) = 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pathSite_zero,
        pathSite_succ]
      exact signDir01_pointwise_cancel x
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        rZeroA (trivialU witnessL) b.1.1 x signDir01SuTwo b.2 witnessEll = 0 := by
      intro x _
      rw [rZeroA_trivialU]
      apply Finset.sum_eq_zero
      intro i _
      simp only [signDir01SuTwo]
      rw [if_neg hmu]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]

theorem signDir01_mem_subspace156G (ell : ℕ) :
    signDir01SuTwo ∈ subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell
      (trivialU witnessL) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro b hb; exact absurd (Finset.mem_univ b.1) hb
  · intro y hy; exact absurd hy (Finset.notMem_empty y)
  · exact signDir01_mem_kernel

/-- At `trivialU` the covariant divergence collapses to its direction-`0` term (the field vanishes
on the other two directions). -/
theorem adj_trivialU_signDir01 (y : PeriodicLatticeSite witnessL) :
    gradCovariantAdjointValue (trivialU witnessL) signDir01SuTwo y =
      signDir01SuTwo (periodicLatticeShiftBack y 0, (0 : Fin 3))
        - signDir01SuTwo (y, (0 : Fin 3)) := by
  unfold gradCovariantAdjointValue
  rw [Fin.sum_univ_three]
  have hU : ∀ b : Bond witnessL, ((trivialU witnessL) b)⁻¹
      = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
    intro b; show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = 1; simp
  simp only [hU, RMap_one, LinearMap.id_coe, id_eq]
  have h1 : signDir01SuTwo (periodicLatticeShiftBack y 1, (1 : Fin 3)) = 0 := by
    simp [signDir01SuTwo]
  have h1' : signDir01SuTwo (y, (1 : Fin 3)) = 0 := by simp [signDir01SuTwo]
  have h2 : signDir01SuTwo (periodicLatticeShiftBack y 2, (2 : Fin 3)) = 0 := by
    simp [signDir01SuTwo]
  have h2' : signDir01SuTwo (y, (2 : Fin 3)) = 0 := by simp [signDir01SuTwo]
  rw [h1, h1', h2, h2']
  abel

theorem sign_at_shiftBack_witnessY :
    signDir01SuTwo (periodicLatticeShiftBack witnessY 0, (0 : Fin 3)) = -suTwoWitness := by
  have hval : ((periodicLatticeShiftBack witnessY 0) 0).val
      + ((periodicLatticeShiftBack witnessY 0) 1).val = 3 := by decide
  rw [signDir01_dir0, hval]; norm_num

theorem sign_at_witnessY : signDir01SuTwo (witnessY, (0 : Fin 3)) = suTwoWitness := by
  have hval : ((witnessY : PeriodicLatticeSite witnessL) 0).val
      + ((witnessY : PeriodicLatticeSite witnessL) 1).val = 0 := by decide
  rw [signDir01_dir0, hval]; norm_num

theorem sign_at_shiftBack_shift1 :
    signDir01SuTwo (periodicLatticeShiftBack (periodicLatticeShift witnessY 1) 0, (0 : Fin 3))
      = suTwoWitness := by
  have hval : ((periodicLatticeShiftBack (periodicLatticeShift witnessY 1) 0) 0).val
      + ((periodicLatticeShiftBack (periodicLatticeShift witnessY 1) 0) 1).val = 4 := by decide
  rw [signDir01_dir0, hval]; norm_num

theorem sign_at_shift1 :
    signDir01SuTwo (periodicLatticeShift witnessY 1, (0 : Fin 3)) = -suTwoWitness := by
  have hval : ((periodicLatticeShift witnessY 1) 0).val
      + ((periodicLatticeShift witnessY 1) 1).val = 1 := by decide
  rw [signDir01_dir0, hval]; norm_num

/-- **THE DISTINGUISHING VALUE**: `D_1 D_1^* signDir01SuTwo` is `4 • suTwoWitness` at the
direction-`1` bond `(witnessY, 1)`, where `signDir01SuTwo` itself is `0`. -/
theorem bondLaplacian_signDir01_at_witnessY_dir1 :
    bondLaplacianCovLM (trivialU witnessL) signDir01SuTwo (witnessY, (1 : Fin 3))
      = (4 : ℝ) • suTwoWitness := by
  rw [bondLaplacianCovLM_apply]
  show RMap ((trivialU witnessL) (witnessY, (1 : Fin 3)))
      (gradCovariantAdjointValue (trivialU witnessL) signDir01SuTwo
        (periodicLatticeShift witnessY 1))
      - gradCovariantAdjointValue (trivialU witnessL) signDir01SuTwo witnessY = _
  have hU : (trivialU witnessL) (witnessY, (1 : Fin 3))
      = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := rfl
  rw [hU, RMap_one, adj_trivialU_signDir01, adj_trivialU_signDir01,
    sign_at_shiftBack_shift1, sign_at_shift1, sign_at_shiftBack_witnessY, sign_at_witnessY]
  show (suTwoWitness - -suTwoWitness) - (-suTwoWitness - suTwoWitness) = (4 : ℝ) • suTwoWitness
  module

/-- **`D_1 D_1^*` is not a scalar multiple of the identity ON the witness** — for EVERY `c`. -/
theorem signDir01_not_scalar :
    ∀ c : ℝ, bondLaplacianCovLM (trivialU witnessL) signDir01SuTwo ≠ c • signDir01SuTwo := by
  intro c h
  have hpt := congrFun h (witnessY, (1 : Fin 3))
  rw [bondLaplacian_signDir01_at_witnessY_dir1] at hpt
  have hA : signDir01SuTwo (witnessY, (1 : Fin 3)) = 0 := by simp [signDir01SuTwo]
  rw [Pi.smul_apply, hA, smul_zero] at hpt
  rcases smul_eq_zero.mp hpt with h4 | hw
  · norm_num at h4
  · exact suTwoWitness_ne_zero hw

/-- **THE §7c DELIVERABLE**: at `trivialU`, `D_U D_U^*` is not `c · id` on the admissible subspace
for ANY `c` — including `c = 0`, which §7b's dimension argument cannot reach. -/
theorem bondLaplacianCov_not_scalar_on_subspace156G_trivialU (ell : ℕ) (c : ℝ) :
    ¬ (∀ v ∈ subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell
        (trivialU witnessL), bondLaplacianCovLM (trivialU witnessL) v = c • v) := by
  intro hscal
  exact signDir01_not_scalar c (hscal signDir01SuTwo (signDir01_mem_subspace156G ell))

#print axioms signDir01SuTwo
#print axioms signDir01_dir0
#print axioms signDir01_pointwise_cancel
#print axioms signDir01_mem_kernel
#print axioms signDir01_mem_subspace156G
#print axioms adj_trivialU_signDir01
#print axioms sign_at_shiftBack_witnessY
#print axioms sign_at_witnessY
#print axioms sign_at_shiftBack_shift1
#print axioms sign_at_shift1
#print axioms bondLaplacian_signDir01_at_witnessY_dir1
#print axioms signDir01_not_scalar
#print axioms bondLaplacianCov_not_scalar_on_subspace156G_trivialU

/-! ### §7d — `c = 0` IS KILLED TOO, at `Λ := univ`, `S' := ∅`, for EVERY `U`

**Correction to §7's own header, made in the same pass (S75).** That header stated that
`hsInner` has no `hsInner_self_eq_zero` anywhere in the tree. ~~That was WRONG~~ — the grep behind it
was scoped to three files. `SuTwoInner.lean:148` proves exactly
`hsInner_self_eq_zero {X : SuTwo} (h : hsInner X X = 0) : X = 0`, and it is already used at
`CovU1Reduction.lean:180`. Since the missing primitive was in fact present, the case is not a
residual: it is closed below.

Two steps, both `U`-uniform:

1. **`ker (D_U D_U^*) = ker D_U^*`** (`ker_bondLaplacian_eq_ker_gradAdjoint`), from
   `BondSU2Space.covBondInner_bondLaplacianCovLM_eq_covSiteInner` plus definiteness of `covSiteInner`
   (`covSiteInner_self_eq_zero`, proved here from `hsInner_self_eq_zero` termwise).
2. **`rank D_U^* ≥ 32 · dim 𝔰𝔲(2)`, for EVERY `U`** (`finrank_range_gradAdjoint_lower`), by a SCATTER
   argument that needs no property of `U` at all: on the 32 direction-`0` bonds whose base site has
   EVEN `x₀`, the covariant divergence is DIAGONAL — at such a site `y` the `μ = 0` predecessor bond
   `(y − e₀, 0)` has ODD `x₀` and so is outside the family, and the `μ = 1, 2` terms vanish because
   the family is direction-`0` only. So `(D_U^* (scatter f))(y) = −f(y,0)` exactly, and the composite
   is injective.

Then `dim ker D_U^* ≤ (192 − 32)·dim 𝔰𝔲(2) = 160·dim 𝔰𝔲(2)`, while `dim V ≥ 168·dim 𝔰𝔲(2)` at
`Λ := univ`, `S' := ∅` (§4), so `V ⊄ ker D_U^*` and `c = 0` is impossible.

~~**Where this does NOT reach, with the exact arithmetic.** At the §5 non-degenerate parameter point
`dim V ≥ 158·dim 𝔰𝔲(2)`, and `158 < 160`, so the 32-bond scatter is one notch too weak there: that
point needs `rank D_U^* > 34 · dim 𝔰𝔲(2)`. The refinement is identified — take the 48 direction-`0`
bonds with `x₀ ≤ 2` instead; the same evaluation is then LOWER-TRIANGULAR (at `x₀ = 0` the
predecessor is outside the family; at `x₀ = 1, 2` it lies in the strictly earlier layer) with `−id` on
the diagonal, giving `rank D_U^* ≥ 48 · dim 𝔰𝔲(2)` and `dim ker D_U^* ≤ 144 · dim 𝔰𝔲(2) < 158`. Not
built here; the triangular induction over the three layers is the only extra content.~~

⚠ **SUPERSEDED BY §8 (S75).** Built: `finrank_ker_gradAdjoint_upper48` gives
`dim ker D_U^* ≤ 144 · dim 𝔰𝔲(2)` for every `U`. The induction runs FORWARD (`x₀ = 0` first, where the
predecessor is outside the family and the transported term vanishes by linearity alone), not
backward, so no injectivity of any transport is used — and it is proved at ARBITRARY linear
transports, not only at `R((U b)⁻¹)`. The `158` premise was also not sharp: the deduplicated count is
`161` (§8 (1)), which beats `160` without the refinement at all. -/

open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_self_nonneg hsInner_self_eq_zero)
open AdalyFormal.Balaban.CovariantHj (covBondInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (covSiteInner gradCovariantAdjointLM_apply)
open AdalyFormal.Balaban.BondSU2Space (covBondInner_bondLaplacianCovLM_eq_covSiteInner)

/-- **`covSiteInner` is DEFINITE** — termwise from `SuTwoInner.hsInner_self_eq_zero`, which the tree
already had (see this section's header correction). -/
theorem covSiteInner_self_eq_zero {A : PeriodicLatticeSite witnessL → SuTwo}
    (h : covSiteInner A A = 0) : A = 0 := by
  funext y
  have hnn : ∀ x ∈ (Finset.univ : Finset (PeriodicLatticeSite witnessL)),
      0 ≤ hsInner (A x) (A x) := fun x _ => hsInner_self_nonneg (A x)
  have hsum : ∑ x : PeriodicLatticeSite witnessL, hsInner (A x) (A x) = 0 := h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  exact hsInner_self_eq_zero (hz y (Finset.mem_univ y))

theorem covBondInner_zero_right (A : Bond witnessL → SuTwo) :
    covBondInner A (0 : Bond witnessL → SuTwo) = 0 := by
  show ∑ b : Bond witnessL, hsInner (A b) ((0 : Bond witnessL → SuTwo) b) = 0
  apply Finset.sum_eq_zero
  intro b _
  show hsInner (A b) (0 : SuTwo) = 0
  show -(1 / 2 : ℝ) * (Matrix.trace ((A b : Matrix (Fin 2) (Fin 2) ℂ)
    * ((0 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))).re = 0
  simp

/-- **`ker (D_U D_U^*) = ker D_U^*`, for EVERY `U`** — the Gram identity plus definiteness. -/
theorem ker_bondLaplacian_eq_ker_gradAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (bondLaplacianCovLM U) = LinearMap.ker (gradCovariantAdjointLM U) := by
  apply le_antisymm
  · intro A hA
    rw [LinearMap.mem_ker] at hA
    rw [LinearMap.mem_ker, gradCovariantAdjointLM_apply]
    have hq := covBondInner_bondLaplacianCovLM_eq_covSiteInner U A
    rw [hA, covBondInner_zero_right] at hq
    exact covSiteInner_self_eq_zero hq.symm
  · exact LinearMap.ker_le_ker_comp _ _

/-- The 32 direction-`0` bonds whose base site has EVEN `x₀`. -/
def evenDir0Bonds : Finset (Bond witnessL) :=
  Finset.univ.filter (fun b => b.2 = (0 : Fin 3) ∧ (b.1 0).val % 2 = 0)

theorem card_evenDir0Bonds : evenDir0Bonds.card = 32 := by decide

theorem mem_evenDir0Bonds {b : Bond witnessL} :
    b ∈ evenDir0Bonds ↔ b.2 = (0 : Fin 3) ∧ (b.1 0).val % 2 = 0 := by
  simp [evenDir0Bonds]

/-- The predecessor of an even-`x₀` site in direction `0` has ODD `x₀` — so its direction-`0` bond is
OUTSIDE `evenDir0Bonds`. This is what makes the scatter evaluation diagonal. Side length `4` is even,
so the parity alternation is consistent across the periodic identification. -/
theorem shiftBack_coord0_odd (y : PeriodicLatticeSite witnessL) (hy : (y 0).val % 2 = 0) :
    ((periodicLatticeShiftBack y 0) 0).val % 2 = 1 := by
  have hval : (periodicLatticeShiftBack y 0) 0 = y 0 - 1 := by
    simp [periodicLatticeShiftBack, Function.update_self]
  rw [hval]
  revert hy
  generalize y 0 = v
  fin_cases v <;> decide

noncomputable def scatterEven :
    ({b : Bond witnessL // b ∈ evenDir0Bonds} → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo) where
  toFun f := fun b => if h : b ∈ evenDir0Bonds then f ⟨b, h⟩ else 0
  map_add' f g := by
    funext b; by_cases h : b ∈ evenDir0Bonds <;> simp [h]
  map_smul' c f := by
    funext b; by_cases h : b ∈ evenDir0Bonds <;> simp [h]

theorem scatterEven_apply_mem (f : {b : Bond witnessL // b ∈ evenDir0Bonds} → SuTwo)
    {b : Bond witnessL} (h : b ∈ evenDir0Bonds) : scatterEven f b = f ⟨b, h⟩ := by
  show (if h' : b ∈ evenDir0Bonds then f ⟨b, h'⟩ else 0) = _
  rw [dif_pos h]

theorem scatterEven_apply_notMem (f : {b : Bond witnessL // b ∈ evenDir0Bonds} → SuTwo)
    {b : Bond witnessL} (h : b ∉ evenDir0Bonds) : scatterEven f b = 0 := by
  show (if h' : b ∈ evenDir0Bonds then f ⟨b, h'⟩ else 0) = _
  rw [dif_neg h]

/-- **THE DIAGONAL EVALUATION** — at an even-`x₀` site the covariant divergence of a scattered field
reads off exactly one coefficient, for EVERY `U`. -/
theorem adj_scatterEven_at_even
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (f : {b : Bond witnessL // b ∈ evenDir0Bonds} → SuTwo) (y : PeriodicLatticeSite witnessL)
    (hy : (y 0).val % 2 = 0) :
    gradCovariantAdjointValue U (scatterEven f) y
      = - f ⟨(y, (0 : Fin 3)), mem_evenDir0Bonds.mpr ⟨rfl, hy⟩⟩ := by
  unfold gradCovariantAdjointValue
  rw [Fin.sum_univ_three]
  have hpred : (periodicLatticeShiftBack y 0, (0 : Fin 3)) ∉ evenDir0Bonds := by
    intro hmem
    have := (mem_evenDir0Bonds.mp hmem).2
    rw [shiftBack_coord0_odd y hy] at this
    exact absurd this (by decide)
  have hne1 : ¬ ((1 : Fin 3) = 0) := by decide
  have hne2 : ¬ ((2 : Fin 3) = 0) := by decide
  have hd1 : (periodicLatticeShiftBack y 1, (1 : Fin 3)) ∉ evenDir0Bonds := by
    intro hmem; exact absurd ((mem_evenDir0Bonds.mp hmem).1 : (1 : Fin 3) = 0) hne1
  have hd1' : (y, (1 : Fin 3)) ∉ evenDir0Bonds := by
    intro hmem; exact absurd ((mem_evenDir0Bonds.mp hmem).1 : (1 : Fin 3) = 0) hne1
  have hd2 : (periodicLatticeShiftBack y 2, (2 : Fin 3)) ∉ evenDir0Bonds := by
    intro hmem; exact absurd ((mem_evenDir0Bonds.mp hmem).1 : (2 : Fin 3) = 0) hne2
  have hd2' : (y, (2 : Fin 3)) ∉ evenDir0Bonds := by
    intro hmem; exact absurd ((mem_evenDir0Bonds.mp hmem).1 : (2 : Fin 3) = 0) hne2
  rw [scatterEven_apply_notMem f hpred, scatterEven_apply_notMem f hd1,
    scatterEven_apply_notMem f hd1', scatterEven_apply_notMem f hd2,
    scatterEven_apply_notMem f hd2',
    scatterEven_apply_mem f (mem_evenDir0Bonds.mpr ⟨rfl, hy⟩)]
  simp

noncomputable def adjScatter
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ({b : Bond witnessL // b ∈ evenDir0Bonds} → SuTwo) →ₗ[ℝ]
      (PeriodicLatticeSite witnessL → SuTwo) :=
  (gradCovariantAdjointLM U).comp scatterEven

theorem adjScatter_ker_eq_bot
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (adjScatter U) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_bot]
  funext bb
  obtain ⟨b, hb⟩ := bb
  obtain ⟨hb2, hbe⟩ := mem_evenDir0Bonds.mp hb
  have hval : gradCovariantAdjointValue U (scatterEven f) b.1 = 0 := by
    have := congrFun hf b.1
    rw [show adjScatter U f = gradCovariantAdjointValue U (scatterEven f) from rfl] at this
    exact this
  rw [adj_scatterEven_at_even U f b.1 hbe] at hval
  have hbeq : (⟨(b.1, (0 : Fin 3)), mem_evenDir0Bonds.mpr ⟨rfl, hbe⟩⟩ :
      {b : Bond witnessL // b ∈ evenDir0Bonds}) = ⟨b, hb⟩ := by
    apply Subtype.ext
    exact Prod.ext rfl hb2.symm
  rw [hbeq] at hval
  have : f ⟨b, hb⟩ = 0 := by
    have h2 := neg_eq_zero.mp hval
    exact h2
  exact this

theorem finrank_scatterDomain :
    Module.finrank ℝ ({b : Bond witnessL // b ∈ evenDir0Bonds} → SuTwo)
      = 32 * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_pi_fintype (R := ℝ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe, card_evenDir0Bonds]

/-- **`rank D_U^* ≥ 32 · dim 𝔰𝔲(2)`, for EVERY `U`** — no property of `U` is used. -/
theorem finrank_range_gradAdjoint_lower
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    32 * Module.finrank ℝ SuTwo
      ≤ Module.finrank ℝ (LinearMap.range (gradCovariantAdjointLM U)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (adjScatter U)
  rw [adjScatter_ker_eq_bot, finrank_bot, add_zero, finrank_scatterDomain] at hrn
  have hsub : LinearMap.range (adjScatter U) ≤ LinearMap.range (gradCovariantAdjointLM U) :=
    LinearMap.range_comp_le_range _ _
  have hmono := Submodule.finrank_mono hsub
  omega

/-- **`dim ker D_U^* ≤ 160 · dim 𝔰𝔲(2)`, for EVERY `U`.** -/
theorem finrank_ker_gradAdjoint_upper
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Module.finrank ℝ (LinearMap.ker (gradCovariantAdjointLM U)) + 32 * Module.finrank ℝ SuTwo
      ≤ 192 * Module.finrank ℝ SuTwo := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (gradCovariantAdjointLM U)
  rw [finrank_bondFn] at hrn
  have h := finrank_range_gradAdjoint_lower U
  omega

#print axioms covSiteInner_self_eq_zero
#print axioms covBondInner_zero_right
#print axioms ker_bondLaplacian_eq_ker_gradAdjoint
#print axioms evenDir0Bonds
#print axioms mem_evenDir0Bonds
#print axioms scatterEven
#print axioms scatterEven_apply_mem
#print axioms scatterEven_apply_notMem
#print axioms adjScatter
#print axioms finrank_scatterDomain
#print axioms card_evenDir0Bonds
#print axioms shiftBack_coord0_odd
#print axioms adj_scatterEven_at_even
#print axioms adjScatter_ker_eq_bot
#print axioms finrank_range_gradAdjoint_lower
#print axioms finrank_ker_gradAdjoint_upper

/-- **`c = 0` IS IMPOSSIBLE at `Λ := univ`, `S' := ∅`, for EVERY `U`**: `V ⊆ ker (D_U D_U^*)` would
force `168 · dim 𝔰𝔲(2) ≤ 160 · dim 𝔰𝔲(2)`. -/
theorem bondLaplacianCov_not_zero_scalar_univ_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ¬ (∀ v ∈ subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U,
        bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  intro hscal
  have hs := finrank_suTwo_pos
  have hle : subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U
      ≤ LinearMap.ker (gradCovariantAdjointLM U) := by
    rw [← ker_bondLaplacian_eq_ker_gradAdjoint]
    intro v hv
    rw [LinearMap.mem_ker]
    have := hscal v hv
    rw [zero_smul] at this
    exact this
  have hmono := Submodule.finrank_mono hle
  have hupper := finrank_ker_gradAdjoint_upper U
  have hlow := finrank_subspace156G_lower
    (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U
  have h1 : (outsideBonds (Finset.univ : Finset (PeriodicLatticeSite witnessL))).card = 0 := by
    simp [outsideBonds]
  have h2 : (axBonds (∅ : Finset (PeriodicLatticeSite witnessL)) ell).card = 0 := by
    simp [axBonds]
  rw [h1, h2] at hlow
  omega

/-- **THE §7 HEADLINE, ASSEMBLED: `D_U D_U^*` is NOT `c · id` on the admissible subspace, for EVERY
real `c` and EVERY background `U`.** `c ≠ 0` by §7b, `c = 0` by §7d — both by dimension, neither
needing a witness or a flatness assumption. -/
theorem bondLaplacianCov_not_scalar_on_subspace156G_univ_empty (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ) :
    ¬ (∀ v ∈ subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U,
        bondLaplacianCovLM U v = c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact bondLaplacianCov_not_zero_scalar_univ_empty ell U
  · exact bondLaplacianCov_not_nonzero_scalar_univ_empty ell U c hc

#print axioms bondLaplacianCov_not_zero_scalar_univ_empty
#print axioms bondLaplacianCov_not_scalar_on_subspace156G_univ_empty

/-! ## §8 — `c = 0` CLOSED AT THE §5 NON-DEGENERATE PARAMETER POINT, FOUR INDEPENDENT WAYS,
AND A GENERAL THEOREM IN `Λ`, `S'`, `ell`, `U`, `c`

§7d left exactly one case open: `c = 0` at a PROPER `Λ` and NONEMPTY `S'`, where §5's
`dim V ≥ 158·dim 𝔰𝔲(2)` lost to the 32-bond scatter's `dim ker D_U^* ≤ 160·dim 𝔰𝔲(2)`. It is closed
here. Two things were wrong with that framing, and both are fixed:

**(1) THE `158` WAS NOT SHARP — the two locus clauses OVERLAP, and §3 counted the overlap twice.**
`outsideBonds (univ.erase witnessY)` is exactly the three bonds BASED at `witnessY = (0,0,0)`
(`outsideBonds` filters on `b.1 ∉ Λ`), and all three of them already lie in
`Ax witnessY witnessEll` — `AxialContour.lean` §4's own decomposition of that 7-bond set is
`1` trunk bond in direction `2` at the origin, `2` branch bonds in direction `1`, `4` leaf bonds in
direction `0`. **Verified here in the kernel, not taken on report**:
`outsideBonds_subset_axBonds_nondegenerate` and `card_union_nondegenerate` are `decide`, and the
must-not-fire companion `outsideBonds_not_subset_axBonds_lambda_empty` shows the inclusion is a fact
about THIS parameter point rather than a general identity (it FAILS at `Λ := ∅`). §3's `ClauseCod` is
a PRODUCT of the two restriction codomains, so it charges `3 + 7`; the deduplicated `ClauseCodU`
restricts once, to the UNION, and charges `7`. Hence
`161·dim 𝔰𝔲(2) ≤ dim V` (`finrank_subspace156G_nondegenerate_sharp`), and `161 > 160` closes `c = 0`
against the ALREADY-FILED `finrank_ker_gradAdjoint_upper` with no new geometry at all
(`not_zero_scalar_nondegenerate_dedup`).

**(2) THE 48-BOND TRIANGULAR SCATTER §7d NAMED IS ALSO BUILT, and gives much more than the notch —
and it is built as a GENERAL CRITERION, not as one family.** `scatterTriangular_eq_zero`: a bond
family `T` is scatter-injective, at ARBITRARY linear transports hence at every `U`, as soon as it
carries a rank function `ρ` with (i) no two bonds of `T` sharing a BASE SITE, and (ii) every bond of
`T` ENDING at the base site of `b ∈ T` having strictly smaller `ρ`. The equation at the base site of
`b` then reads off `f b = 0` once the strictly-earlier coefficients are known, and a strong induction
on `ρ` kills all of them. `layerDir0Bonds` — the 48 direction-`0` bonds with `x₀ ≤ 2`
(`card_layerDir0Bonds`, `decide`) — is the instance `ρ b = (b.1 0).val`: base-injective because every
bond of the family has direction `0`, and strictly decreasing because at `x₀ = 0` the direction-`0`
predecessor has `x₀ = 3` and is OUTSIDE the family, so the transported term is `Φ(…) 0 = 0` by
LINEARITY ALONE. The induction therefore runs FORWARD and needs the injectivity of NO parallel
transport anywhere. Consequences, all uniform in `U`: `rank D_U^* ≥ 48·dim 𝔰𝔲(2)`,
`dim ker D_U^* ≤ 144·dim 𝔰𝔲(2)`. Any consumer facing a different `Λ` can supply its own `(T, ρ)`
rather than re-deriving an induction (LAW-19).

**S82 GARBAGE SUBSTITUTION, DISCHARGED AS A THEOREM.** The whole layer argument is proved at an
ARBITRARY family of linear transports `Φ : Bond → (𝔰𝔲(2) →ₗ 𝔰𝔲(2))` (`genDivValue`), with
`gradCovariantAdjointValue U` recovered as the instance `Φ b = R((U b)⁻¹)` by `rfl`
(`genDivValue_eq`). It therefore also holds at the STRUCTURALLY INVALID `Φ := 0`
(`scatterLayer_eq_zero_zeroTransport`). That is the honest disclosure: the content of the 48-bond
bound is the forward triangular order on the `x₀ ≤ 2` layers, NOT the covariance — exactly as §3c
disclosed that §4's content is the corank count and not a property of `Q₀`.

**THE CRITERION THAT IS ACTUALLY SHARP (`not_zero_scalar_of_transverse`).** Both routes above are
GLOBAL: they compare `dim V` with `dim ker D_U^*` over the whole 192-bond space. The sharp statement
is RELATIVE and carries no global cardinality hypothesis whatsoever: writing
`W := Λ-clause ⊓ Ax-clause`, `c = 0` dies as soon as `W` contains a subspace of dimension
`> 24·dim 𝔰𝔲(2)` meeting `ker D_U^*` only in `0`. `24·dim 𝔰𝔲(2)` is exactly the codomain of `Q₁`,
i.e. the most the third clause can cost (`finrank_locusW_le`). Its concrete, decidable form
(`not_zero_scalar_of_allowed`): **more than 24 of the 48 layer bonds survive `Λ` and `Ax`.** At the
§5 point 44 survive (`card_allowedLayerBonds_nondegenerate`, `decide`).

**THE §5 POINT IS THEREFORE CLOSED FOUR TIMES OVER**, by arguments sharing neither the family nor the
count: the dedup (`161 > 160`), the global 48-bond scatter (`34 < 48`), the relative criterion
(`44 > 24`), and the general theorem (`|union| = 7 ≤ 23`). `bondLaplacianCov_not_scalar_nondegenerate`
is the assembled headline: **for EVERY real `c` and EVERY background `U`, `D_U D_U^*` is not `c·id` on
the admissible subspace at a PROPER `Λ` and a NONEMPTY `S'`** — instantiated at the tree's own
non-flat `CovariantOperators.witnessU` in `bondLaplacianCov_not_scalar_nondegenerate_witnessU`.

**WHERE THE METHOD SATURATES — the answer to "why not the full §4 hypothesis".** §4's cardinality
hypothesis permits `|union| ≤ 166`. The GLOBAL comparison provably cannot run past `|union| = 39`:
`dim ker D_U^* ≥ 128·dim 𝔰𝔲(2)` for EVERY `U` (rank–nullity against 64 sites), while the deduplicated
lower bound on `dim V` is `(168 − |union|)·dim 𝔰𝔲(2)`, and at `|union| ≥ 40` the latter no longer
exceeds the former — `global_route_saturates_union`. The `c ≠ 0` comparison stops at `|union| = 103`
for the same reason (`nonzero_route_saturates_union`). And no scatter family can help past that:
`scatter_card_le_64` (the codomain of `D_U^*` is `64·dim 𝔰𝔲(2)`), sharpened at a flat background to
`scatter_card_le_63_trivialU` — the covariant divergence at `trivialU` telescopes into the sum-zero
subspace (`sum_gradAdjoint_trivialU`), so `64` is unreachable and a spanning tree's `63` is the
ceiling; the family used here is `48`. **The distance from `40` to `166` is not a missing lemma, it is
the ceiling of dimension counting against `ker D_U^*`.** The RELATIVE criterion is the one route that
is not bounded by it — its hypothesis constrains only how many LAYER bonds are lost, not how many
bonds are forbidden in total, and it holds with up to `144` forbidden bonds
(`bondLaplacianCov_not_scalar_general_union`).

**MUST-FIRE CONTROL (§CONTROL), fired rather than imagined.** The `x₀ ≤ 2` restriction defining the
48-bond family is LOAD-BEARING and this is proved by counterexample, not asserted: with all 64
direction-`0` bonds the injectivity is FALSE (`adjScatterT_full_ker_ne_bot`), witnessed by the field
that is CONSTANT along every direction-`0` line — each such line closes into a cycle, so its covariant
divergence vanishes identically at a flat background. This is also exactly what
`scatter_card_le_63_trivialU` predicts (`64 > 63`), so the ceiling theorem and the counterexample
corroborate each other by different means.

**MUST-NOT-FIRE CONTROLS (§CONTROL), watched rather than asserted.** At `Λ := ∅` the conclusion of
every theorem in this section is FALSE — the subspace is `⊥`, so `D_U D_U^*` IS `c·id` on it for
every `c` (`scalar_holds_at_lambda_empty`, proved). Each hypothesis is refuted exactly there:
`allowedHyp_fails_at_lambda_empty` (no layer bond survives), `globalHyp_fails_at_lambda_empty`
(`192 + 24 < 48` is false), and `outsideBonds_not_subset_axBonds_lambda_empty` (the dedup inclusion
fails). §DEGEN: at `ell = 0` clause 2 is vacuous and MORE bonds survive
(`card_allowedLayerBonds_ell_zero` = 47), recorded so no reader treats a small-`ell` instance as
evidence that clause 2 constrains anything.

**WHAT THIS IS NOT.** This is a statement about `bondLaplacianCovLM U = D_U D_U^*` on
`subspace156G` at `witnessL`. It is NOT `Spine.coerc_u_main`'s non-scalarity conjunct, and must not be
cited as it; the two differ in FIVE respects: **carrier** (`Bond witnessL → SuTwo` here vs
`AnchoredBondSpace Lat` there), **lattice** (one hard-coded `witnessL` here vs arbitrary `Lat`),
**operator** (`D_U D_U^*` here vs the `C`-sandwiched `C* Δ_k C` there), **scale** (no `k` appears
here at all), and **domain of the equality** (a pointwise condition on members of `q1RealKernel U`
here vs an identity of continuous linear maps there). The `C`-sandwiched form remains unaddressed, as
§7 already recorded.

**Reuses, does not rebuild** (LAW-19): §7d's `scatterEven`/`adjScatter` are the `T := evenDir0Bonds`
instances of `scatterT`/`adjScatterT` (`scatterEven_eq`, `adjScatter_eq`, both `rfl`), and §7d's
`finrank_scatterDomain` is the `T := evenDir0Bonds` instance of `finrank_scatterT_domain`. Nothing
outside this file is edited. -/

/-! ## generic scatter -/

noncomputable def scatterT (T : Finset (Bond witnessL)) :
    ({b : Bond witnessL // b ∈ T} → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo) where
  toFun f := fun b => if h : b ∈ T then f ⟨b, h⟩ else 0
  map_add' f g := by funext b; by_cases h : b ∈ T <;> simp [h]
  map_smul' c f := by funext b; by_cases h : b ∈ T <;> simp [h]

theorem scatterT_apply_mem {T : Finset (Bond witnessL)}
    (f : {b : Bond witnessL // b ∈ T} → SuTwo) {b : Bond witnessL} (h : b ∈ T) :
    scatterT T f b = f ⟨b, h⟩ := by
  show (if h' : b ∈ T then f ⟨b, h'⟩ else 0) = _
  rw [dif_pos h]

theorem scatterT_apply_notMem {T : Finset (Bond witnessL)}
    (f : {b : Bond witnessL // b ∈ T} → SuTwo) {b : Bond witnessL} (h : b ∉ T) :
    scatterT T f b = 0 := by
  show (if h' : b ∈ T then f ⟨b, h'⟩ else 0) = _
  rw [dif_neg h]

noncomputable def adjScatterT (T : Finset (Bond witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ({b : Bond witnessL // b ∈ T} → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite witnessL → SuTwo) :=
  (gradCovariantAdjointLM U).comp (scatterT T)

/-- The §7d objects are the `T := evenDir0Bonds` members of this family. -/
theorem scatterEven_eq : scatterEven = scatterT evenDir0Bonds := rfl

theorem adjScatter_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : adjScatter U = adjScatterT evenDir0Bonds U := rfl

/-! ## the 48-bond layer family -/

def layerDir0Bonds : Finset (Bond witnessL) :=
  Finset.univ.filter (fun b => b.2 = (0 : Fin 3) ∧ (b.1 0).val ≤ 2)

theorem mem_layerDir0Bonds {b : Bond witnessL} :
    b ∈ layerDir0Bonds ↔ b.2 = (0 : Fin 3) ∧ (b.1 0).val ≤ 2 := by
  simp [layerDir0Bonds]

theorem card_layerDir0Bonds : layerDir0Bonds.card = 48 := by decide

/-- **THE TRANSPORT IS ARBITRARY (S82).** The divergence with an ARBITRARY family of linear
transports `Φ` — `gradCovariantAdjointValue U` is the special case `Φ b = R((U b)⁻¹)`
(`genDivValue_eq`, `rfl`). Everything about the 48-bond family below is proved at THIS generality,
so no step can be using unitarity, flatness, or any property of `U`. -/
noncomputable def genDivValue (Φ : Bond witnessL → (SuTwo →ₗ[ℝ] SuTwo))
    (A : Bond witnessL → SuTwo) (y : PeriodicLatticeSite witnessL) : SuTwo :=
  ∑ μ : Fin 3,
    (Φ (periodicLatticeShiftBack y μ, μ) (A (periodicLatticeShiftBack y μ, μ)) - A (y, μ))

theorem genDivValue_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) (A : Bond witnessL → SuTwo) (y : PeriodicLatticeSite witnessL) :
    genDivValue (fun b => RMap ((U b)⁻¹)) A y = gradCovariantAdjointValue U A y := rfl

/-- **THE GENERAL TRIANGULAR CRITERION.** A bond family `T` is scatter-injective — at ARBITRARY
linear transports `Φ`, hence at every `U` — as soon as it carries a rank function `ρ` with

* `hbase` : no two bonds of `T` share a BASE SITE, and
* `hin` : every bond of `T` that ENDS at the base site of `b ∈ T` has strictly smaller `ρ`.

Then the equation at the base site of `b` reads off `f b = 0` once every strictly-earlier coefficient
is known, so a strong induction on `ρ` kills all of them. The 48-bond layer family is the instance
`ρ b = (b.1 0).val`. -/
theorem scatterTriangular_eq_zero (T : Finset (Bond witnessL)) (rho : Bond witnessL → ℕ)
    (hbase : ∀ b ∈ T, ∀ b' ∈ T, b.1 = b'.1 → b = b')
    (hin : ∀ b ∈ T, ∀ μ : Fin 3, (periodicLatticeShiftBack b.1 μ, μ) ∈ T →
      rho (periodicLatticeShiftBack b.1 μ, μ) < rho b)
    (Φ : Bond witnessL → (SuTwo →ₗ[ℝ] SuTwo))
    (f : {b : Bond witnessL // b ∈ T} → SuTwo)
    (hf : ∀ y, genDivValue Φ (scatterT T f) y = 0) : f = 0 := by
  have key : ∀ n : ℕ, ∀ b : Bond witnessL, b ∈ T → rho b = n → scatterT T f b = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro ⟨x, μ0⟩ hb hrho
      have hin0 : ∀ μ : Fin 3, scatterT T f (periodicLatticeShiftBack x μ, μ) = 0 := by
        intro μ
        by_cases hm : (periodicLatticeShiftBack x μ, μ) ∈ T
        · have hlt0 : rho (periodicLatticeShiftBack x μ, μ) < rho ((x, μ0) : Bond witnessL) :=
            hin (x, μ0) hb μ hm
          rw [hrho] at hlt0
          exact ih _ hlt0 _ hm rfl
        · exact scatterT_apply_notMem f hm
      have hout : ∀ μ : Fin 3, μ ≠ μ0 → scatterT T f (x, μ) = 0 := by
        intro μ hμ
        by_cases hm : ((x, μ) : Bond witnessL) ∈ T
        · exact absurd (congrArg Prod.snd (hbase (x, μ) hm (x, μ0) hb rfl)) hμ
        · exact scatterT_apply_notMem f hm
      have h := hf x
      unfold genDivValue at h
      rw [Fin.sum_univ_three, hin0 0, hin0 1, hin0 2, map_zero, map_zero, map_zero] at h
      fin_cases μ0
      · rw [hout 1 (by decide), hout 2 (by decide)] at h
        have : -scatterT T f (x, (0 : Fin 3)) = 0 := by rw [← h]; abel
        rw [neg_eq_zero] at this
        exact this
      · rw [hout 0 (by decide), hout 2 (by decide)] at h
        have : -scatterT T f (x, (1 : Fin 3)) = 0 := by rw [← h]; abel
        rw [neg_eq_zero] at this
        exact this
      · rw [hout 0 (by decide), hout 1 (by decide)] at h
        have : -scatterT T f (x, (2 : Fin 3)) = 0 := by rw [← h]; abel
        rw [neg_eq_zero] at this
        exact this
  funext bb
  obtain ⟨b, hb⟩ := bb
  have hval := key (rho b) b hb rfl
  rw [scatterT_apply_mem f hb] at hval
  exact hval

theorem shiftBack_coord0 (y : PeriodicLatticeSite witnessL) :
    (periodicLatticeShiftBack y 0) 0 = y 0 - 1 := by
  simp [periodicLatticeShiftBack, Function.update_self]

theorem shiftBack_coord0_lt (y : PeriodicLatticeSite witnessL)
    (h : ((periodicLatticeShiftBack y 0) 0).val ≤ 2) :
    ((periodicLatticeShiftBack y 0) 0).val < (y 0).val := by
  rw [shiftBack_coord0] at h ⊢
  revert h
  generalize y 0 = v
  fin_cases v <;> decide

/-- **THE 48-BOND LAYER FAMILY IS THE `ρ b = (b.1 0).val` INSTANCE.** Base-injective because every
bond of the family has direction `0`, so its base site determines it; and the only bond of the family
that can END at `x` is `(x − e₀, 0)`, whose `x₀` is strictly smaller — strictly, because if `x₀` were
`0` the predecessor's `x₀` would be `3`, which is OUTSIDE the family (that is the whole content of the
`x₀ ≤ 2` restriction, and §MUSTFIRE below shows dropping it makes the statement FALSE). -/
theorem scatterLayer_eq_zero (Φ : Bond witnessL → (SuTwo →ₗ[ℝ] SuTwo))
    (f : {b : Bond witnessL // b ∈ layerDir0Bonds} → SuTwo)
    (hf : ∀ y, genDivValue Φ (scatterT layerDir0Bonds f) y = 0) : f = 0 := by
  refine scatterTriangular_eq_zero layerDir0Bonds (fun b => (b.1 0).val) ?_ ?_ Φ f hf
  · intro b hb b' hb' hbb
    have h1 : b.2 = (0 : Fin 3) := (mem_layerDir0Bonds.mp hb).1
    have h2 : b'.2 = (0 : Fin 3) := (mem_layerDir0Bonds.mp hb').1
    exact Prod.ext hbb (h1.trans h2.symm)
  · intro b hb μ hm
    have hμ : μ = (0 : Fin 3) := (mem_layerDir0Bonds.mp hm).1
    subst hμ
    exact shiftBack_coord0_lt b.1 (mem_layerDir0Bonds.mp hm).2
/-- **`rank D_U^* ≥ 48·dim 𝔰𝔲(2)` in kernel form, for EVERY `U`.** -/
theorem adjScatterT_layer_ker_eq_bot
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (adjScatterT layerDir0Bonds U) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_bot]
  refine scatterLayer_eq_zero (fun b => RMap ((U b)⁻¹)) f ?_
  intro y
  rw [genDivValue_eq]
  exact congrFun hf y

/-- **S82 GARBAGE SUBSTITUTION, as a theorem.** The same injectivity at the STRUCTURALLY INVALID
transport `Φ := 0` (every parallel transport annihilated). It still holds — which is the honest
disclosure that the 48-bond argument uses NOTHING about the connection beyond linearity: its content
is the forward triangular order on the `x₀ ≤ 2` layers, not the covariance. -/
theorem scatterLayer_eq_zero_zeroTransport
    (f : {b : Bond witnessL // b ∈ layerDir0Bonds} → SuTwo)
    (hf : ∀ y, genDivValue (fun _ => (0 : SuTwo →ₗ[ℝ] SuTwo)) (scatterT layerDir0Bonds f) y = 0) :
    f = 0 := scatterLayer_eq_zero _ f hf

/-! ## rank consequences of an injective scatter -/

theorem finrank_scatterT_domain (T : Finset (Bond witnessL)) :
    Module.finrank ℝ ({b : Bond witnessL // b ∈ T} → SuTwo)
      = T.card * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_pi_fintype (R := ℝ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe]

theorem ker_scatterT_eq_bot {T : Finset (Bond witnessL)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL}
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) : LinearMap.ker (scatterT T) = ⊥ := by
  have h := LinearMap.ker_le_ker_comp (scatterT T) (gradCovariantAdjointLM U)
  rw [show (gradCovariantAdjointLM U).comp (scatterT T) = adjScatterT T U from rfl, hinj] at h
  exact le_bot_iff.mp h

theorem finrank_range_scatterT {T : Finset (Bond witnessL)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL}
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) :
    Module.finrank ℝ (LinearMap.range (scatterT T)) = T.card * Module.finrank ℝ SuTwo := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (scatterT T)
  rw [ker_scatterT_eq_bot hinj, finrank_bot, add_zero, finrank_scatterT_domain] at hrn
  exact hrn

theorem finrank_range_gradAdjoint_lower_of_scatter (T : Finset (Bond witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) :
    T.card * Module.finrank ℝ SuTwo
      ≤ Module.finrank ℝ (LinearMap.range (gradCovariantAdjointLM U)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (adjScatterT T U)
  rw [hinj, finrank_bot, add_zero, finrank_scatterT_domain] at hrn
  have hsub : LinearMap.range (adjScatterT T U) ≤ LinearMap.range (gradCovariantAdjointLM U) :=
    LinearMap.range_comp_le_range _ _
  have hmono := Submodule.finrank_mono hsub
  omega

theorem finrank_ker_gradAdjoint_upper_of_scatter (T : Finset (Bond witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) :
    Module.finrank ℝ (LinearMap.ker (gradCovariantAdjointLM U))
        + T.card * Module.finrank ℝ SuTwo ≤ 192 * Module.finrank ℝ SuTwo := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (gradCovariantAdjointLM U)
  rw [finrank_bondFn] at hrn
  have h := finrank_range_gradAdjoint_lower_of_scatter T U hinj
  omega

/-! ## GLOBAL route, parameterized by whatever lower bound on `dim V` is available -/

/-- `c = 0` dies whenever SOME available lower bound `(192−n)·dim 𝔰𝔲(2)` on `dim V` beats the
scatter's upper bound `(192−#T)·dim 𝔰𝔲(2)` on `dim ker D_U^*`. -/
theorem not_zero_scalar_of_scatter_of_dim
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (T : Finset (Bond witnessL)) (n : ℕ)
    (hlow : 192 * Module.finrank ℝ SuTwo
      ≤ n * Module.finrank ℝ SuTwo + Module.finrank ℝ (subspace156G Lambda S' ell U))
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) (hcard : n < T.card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  intro hscal
  have hs := finrank_suTwo_pos
  have hle : subspace156G Lambda S' ell U ≤ LinearMap.ker (gradCovariantAdjointLM U) := by
    rw [← ker_bondLaplacian_eq_ker_gradAdjoint]
    intro v hv
    rw [LinearMap.mem_ker]
    have h := hscal v hv
    rwa [zero_smul] at h
  have hmono := Submodule.finrank_mono hle
  have hupper := finrank_ker_gradAdjoint_upper_of_scatter T U hinj
  set s := Module.finrank ℝ SuTwo with hsdef
  have hmul : n * s < T.card * s := by
    have hstep : n + 1 ≤ T.card := hcard
    calc n * s < n * s + s := by omega
      _ = (n + 1) * s := by ring
      _ ≤ T.card * s := Nat.mul_le_mul_right s hstep
  omega

/-- The `n := |outside| + |ax| + 24` instance (§3's un-deduplicated count). -/
theorem not_zero_scalar_of_scatter_global
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (T : Finset (Bond witnessL)) (hinj : LinearMap.ker (adjScatterT T U) = ⊥)
    (hcard : (outsideBonds Lambda).card + (axBonds S' ell).card + 24 < T.card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = (0 : ℝ) • v) :=
  not_zero_scalar_of_scatter_of_dim Lambda S' ell U T _
    (finrank_subspace156G_lower Lambda S' ell U) hinj hcard

/-! ## RELATIVE route -/

noncomputable def locusW (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    Submodule ℝ (Bond witnessL → SuTwo) :=
  LambdaComplementLocusG Lambda ⊓ AxUnionLocusG S' ell

theorem subspace156G_eq_inf (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    subspace156G Lambda S' ell U = locusW Lambda S' ell ⊓ q1RealKernel U := rfl

theorem finrank_coarseFn :
    Module.finrank ℝ (CoarseBond witnessL witnessEll → SuTwo) = 24 * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_pi_fintype (R := ℝ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_coarseBond]

theorem finrank_ker_q1Real_lower
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo
      ≤ 24 * Module.finrank ℝ SuTwo + Module.finrank ℝ (q1RealKernel U) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (Q1Real U)
  rw [finrank_bondFn] at hrn
  have hle : Module.finrank ℝ (LinearMap.range (Q1Real U))
      ≤ Module.finrank ℝ (CoarseBond witnessL witnessEll → SuTwo) := Submodule.finrank_le _
  rw [finrank_coarseFn] at hle
  have hk : Module.finrank ℝ (LinearMap.ker (Q1Real U)) = Module.finrank ℝ (q1RealKernel U) := rfl
  omega

/-- `dim W ≤ 24·dim 𝔰𝔲(2) + dim V` — the ONLY thing `Q₁` costs. -/
theorem finrank_locusW_le (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Module.finrank ℝ (locusW Lambda S' ell)
      ≤ 24 * Module.finrank ℝ SuTwo + Module.finrank ℝ (subspace156G Lambda S' ell U) := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (locusW Lambda S' ell) (q1RealKernel U)
  rw [← subspace156G_eq_inf] at hsup
  have hle : Module.finrank ℝ
      ((locusW Lambda S' ell ⊔ q1RealKernel U : Submodule ℝ (Bond witnessL → SuTwo)))
      ≤ Module.finrank ℝ (Bond witnessL → SuTwo) := Submodule.finrank_le _
  rw [finrank_bondFn] at hle
  have hq := finrank_ker_q1Real_lower U
  omega

theorem range_scatterT_le_locusW {T : Finset (Bond witnessL)}
    {Lambda S' : Finset (PeriodicLatticeSite witnessL)} {ell : ℕ}
    (hTin : ∀ b ∈ T, b.1 ∈ Lambda) (hTax : ∀ b ∈ T, b ∉ axBonds S' ell) :
    LinearMap.range (scatterT T) ≤ locusW Lambda S' ell := by
  rintro x ⟨f, rfl⟩
  refine ⟨?_, ?_⟩
  · intro b hb
    refine scatterT_apply_notMem f ?_
    intro hmem
    exact hb (hTin b hmem)
  · intro y hy b hb
    refine scatterT_apply_notMem f ?_
    intro hmem
    exact hTax b hmem (mem_axBonds.mpr ⟨y, hy, hb⟩)

theorem range_scatterT_inf_ker_eq_bot {T : Finset (Bond witnessL)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL}
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) :
    LinearMap.range (scatterT T) ⊓ LinearMap.ker (gradCovariantAdjointLM U) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hxr, hxk⟩ := hx
  obtain ⟨f, hf⟩ := hxr
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hxk
  rw [Submodule.mem_bot]
  have hfk : f ∈ LinearMap.ker (adjScatterT T U) := by
    rw [LinearMap.mem_ker]
    show gradCovariantAdjointLM U (scatterT T f) = 0
    rw [hf]; exact hxk
  rw [hinj, Submodule.mem_bot] at hfk
  rw [← hf, hfk, map_zero]

/-- **THE SHARP CRITERION.** `c = 0` dies as soon as the locus `W = Λ-clause ⊓ Ax-clause` contains
a subspace of dimension `> 24·dim 𝔰𝔲(2)` on which the covariant divergence is injective. No global
cardinality hypothesis at all. `24 · dim 𝔰𝔲(2)` is exactly the codomain of `Q₁`, i.e. the most the
third clause can cost. -/
theorem not_zero_scalar_of_transverse
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (R : Submodule ℝ (Bond witnessL → SuTwo))
    (hRW : R ≤ locusW Lambda S' ell)
    (hRK : R ⊓ LinearMap.ker (gradCovariantAdjointLM U) = ⊥)
    (hRdim : 24 * Module.finrank ℝ SuTwo < Module.finrank ℝ R) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  intro hscal
  have hs := finrank_suTwo_pos
  set s := Module.finrank ℝ SuTwo with hsdef
  set K := LinearMap.ker (gradCovariantAdjointLM U) with hKdef
  set W := locusW Lambda S' ell with hWdef
  have hVK : subspace156G Lambda S' ell U ≤ K := by
    rw [hKdef, ← ker_bondLaplacian_eq_ker_gradAdjoint]
    intro v hv
    rw [LinearMap.mem_ker]
    have h := hscal v hv
    rwa [zero_smul] at h
  have hVW : subspace156G Lambda S' ell U ≤ W := by
    rw [hWdef, subspace156G_eq_inf]; exact inf_le_left
  have hVWK : subspace156G Lambda S' ell U ≤ W ⊓ K := le_inf hVW hVK
  have hRsup := Submodule.finrank_sup_add_finrank_inf_eq R K
  rw [hRK, finrank_bot] at hRsup
  have hWsup := Submodule.finrank_sup_add_finrank_inf_eq W K
  have hmono : Module.finrank ℝ ((R ⊔ K : Submodule ℝ (Bond witnessL → SuTwo)))
      ≤ Module.finrank ℝ ((W ⊔ K : Submodule ℝ (Bond witnessL → SuTwo))) :=
    Submodule.finrank_mono (sup_le_sup_right hRW K)
  have hVle := Submodule.finrank_mono hVWK
  have hWle := finrank_locusW_le Lambda S' ell U
  rw [← hWdef] at hWle
  omega

/-- The scatter form of the criterion: a scatter-injective family of MORE THAN 24 bonds, all of them
left alone by `Λ` and by `Ax`. -/
theorem not_zero_scalar_of_scatter_relative
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (T : Finset (Bond witnessL))
    (hTin : ∀ b ∈ T, b.1 ∈ Lambda) (hTax : ∀ b ∈ T, b ∉ axBonds S' ell)
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) (hcard : 24 < T.card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  refine not_zero_scalar_of_transverse Lambda S' ell U (LinearMap.range (scatterT T))
    (range_scatterT_le_locusW hTin hTax) (range_scatterT_inf_ker_eq_bot hinj) ?_
  rw [finrank_range_scatterT hinj]
  have hs := finrank_suTwo_pos
  have h25 : 25 * Module.finrank ℝ SuTwo ≤ T.card * Module.finrank ℝ SuTwo :=
    Nat.mul_le_mul_right _ hcard
  omega

/-! ## subset monotonicity of scatter-injectivity -/

noncomputable def extZero (T T' : Finset (Bond witnessL)) :
    ({b : Bond witnessL // b ∈ T'} → SuTwo) →ₗ[ℝ] ({b : Bond witnessL // b ∈ T} → SuTwo) where
  toFun f := fun b => if h : b.1 ∈ T' then f ⟨b.1, h⟩ else 0
  map_add' f g := by funext b; by_cases h : (b : Bond witnessL) ∈ T' <;> simp [h]
  map_smul' c f := by funext b; by_cases h : (b : Bond witnessL) ∈ T' <;> simp [h]

theorem scatterT_extZero {T T' : Finset (Bond witnessL)} (hsub : T' ⊆ T)
    (f : {b : Bond witnessL // b ∈ T'} → SuTwo) (b : Bond witnessL) :
    scatterT T (extZero T T' f) b = scatterT T' f b := by
  by_cases h' : b ∈ T'
  · rw [scatterT_apply_mem _ (hsub h'), scatterT_apply_mem _ h']
    show (if h : b ∈ T' then f ⟨b, h⟩ else 0) = f ⟨b, h'⟩
    rw [dif_pos h']
  · rw [scatterT_apply_notMem _ h']
    by_cases h : b ∈ T
    · rw [scatterT_apply_mem _ h]
      show (if h'' : b ∈ T' then f ⟨b, h''⟩ else 0) = 0
      rw [dif_neg h']
    · rw [scatterT_apply_notMem _ h]

theorem ker_adjScatterT_mono {T T' : Finset (Bond witnessL)} (hsub : T' ⊆ T)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (h : LinearMap.ker (adjScatterT T U) = ⊥) : LinearMap.ker (adjScatterT T' U) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_bot]
  have heq : scatterT T (extZero T T' f) = scatterT T' f := by
    funext b; exact scatterT_extZero hsub f b
  have hg : extZero T T' f ∈ LinearMap.ker (adjScatterT T U) := by
    rw [LinearMap.mem_ker]
    show gradCovariantAdjointLM U (scatterT T (extZero T T' f)) = 0
    rw [heq]
    exact hf
  rw [h, Submodule.mem_bot] at hg
  funext b
  have hv : (if hb : (b : Bond witnessL) ∈ T' then f ⟨b.1, hb⟩ else 0) = 0 :=
    congrFun hg ⟨b.1, hsub b.2⟩
  rw [dif_pos b.2] at hv
  exact hv

/-! ## the allowed sub-family and the instantiations -/

def allowedLayerBonds (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    Finset (Bond witnessL) :=
  layerDir0Bonds.filter (fun b => b.1 ∈ Lambda ∧ b ∉ axBonds S' ell)

theorem allowedLayerBonds_subset (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    allowedLayerBonds Lambda S' ell ⊆ layerDir0Bonds := Finset.filter_subset _ _

theorem mem_allowedLayerBonds {Lambda S' : Finset (PeriodicLatticeSite witnessL)} {ell : ℕ}
    {b : Bond witnessL} : b ∈ allowedLayerBonds Lambda S' ell ↔
      b ∈ layerDir0Bonds ∧ (b.1 ∈ Lambda ∧ b ∉ axBonds S' ell) := by
  simp [allowedLayerBonds]

theorem ker_adjScatterT_allowed (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (adjScatterT (allowedLayerBonds Lambda S' ell) U) = ⊥ :=
  ker_adjScatterT_mono (allowedLayerBonds_subset Lambda S' ell) U (adjScatterT_layer_ker_eq_bot U)

/-- **`c = 0` dies whenever more than 24 of the 48 layer bonds survive `Λ` and `Ax`.** -/
theorem not_zero_scalar_of_allowed (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcard : 24 < (allowedLayerBonds Lambda S' ell).card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  refine not_zero_scalar_of_scatter_relative Lambda S' ell U (allowedLayerBonds Lambda S' ell)
    ?_ ?_ (ker_adjScatterT_allowed Lambda S' ell U) hcard
  · intro b hb; exact (mem_allowedLayerBonds.mp hb).2.1
  · intro b hb; exact (mem_allowedLayerBonds.mp hb).2.2

theorem card_allowedLayerBonds_nondegenerate :
    (allowedLayerBonds (Finset.univ.erase witnessY) {witnessY} witnessEll).card = 44 := by decide

/-! ## THE §5 NON-DEGENERATE CLOSURE, two independent ways -/

/-- Route A (global): `n = 3 + 7 + 24 = 34 < 48 = #layer bonds`. -/
theorem not_zero_scalar_nondegenerate_global
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U,
        bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  refine not_zero_scalar_of_scatter_global _ _ witnessEll U layerDir0Bonds
    (adjScatterT_layer_ker_eq_bot U) ?_
  rw [card_outsideBonds_erase_witnessY, card_axBonds_singleton_witnessY, card_layerDir0Bonds]
  omega

/-- Route B (relative): 44 of the 48 layer bonds survive. -/
theorem not_zero_scalar_nondegenerate_relative
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U,
        bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  refine not_zero_scalar_of_allowed _ _ witnessEll U ?_
  rw [card_allowedLayerBonds_nondegenerate]
  omega

/-- **THE HEADLINE AT THE NON-DEGENERATE POINT: every `c`, every `U`, PROPER `Λ`, NONEMPTY `S'`.** -/
theorem bondLaplacianCov_not_scalar_nondegenerate
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U,
        bondLaplacianCovLM U v = c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact not_zero_scalar_nondegenerate_global U
  · exact bondLaplacianCov_not_nonzero_scalar_nondegenerate U c hc

/-- **THE GENERAL HEADLINE.** -/
theorem bondLaplacianCov_not_scalar_general
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ)
    (hcard : (outsideBonds Lambda).card + (axBonds S' ell).card + 24 + 64 ≤ 191)
    (hallow : 24 < (allowedLayerBonds Lambda S' ell).card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact not_zero_scalar_of_allowed Lambda S' ell U hallow
  · exact bondLaplacianCov_not_nonzero_scalar_on_subspace156G Lambda S' ell U hcard c hc

/-! ### the explicit `48` arithmetic §7d's header promised -/

/-- **`rank D_U^* ≥ 48 · dim 𝔰𝔲(2)`, for EVERY `U`** — the refinement §7d named and did not build. -/
theorem finrank_range_gradAdjoint_lower48
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    48 * Module.finrank ℝ SuTwo
      ≤ Module.finrank ℝ (LinearMap.range (gradCovariantAdjointLM U)) := by
  have h := finrank_range_gradAdjoint_lower_of_scatter layerDir0Bonds U
    (adjScatterT_layer_ker_eq_bot U)
  rwa [card_layerDir0Bonds] at h

/-- **`dim ker D_U^* ≤ 144 · dim 𝔰𝔲(2)`, for EVERY `U`.** -/
theorem finrank_ker_gradAdjoint_upper48
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Module.finrank ℝ (LinearMap.ker (gradCovariantAdjointLM U)) + 48 * Module.finrank ℝ SuTwo
      ≤ 192 * Module.finrank ℝ SuTwo := by
  have h := finrank_ker_gradAdjoint_upper_of_scatter layerDir0Bonds U
    (adjScatterT_layer_ker_eq_bot U)
  rwa [card_layerDir0Bonds] at h

/-- All 48 layer bonds survive at `Λ := univ`, `S' := ∅`. -/
theorem allowedLayerBonds_univ_empty (ell : ℕ) :
    allowedLayerBonds (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell
      = layerDir0Bonds := by
  rw [allowedLayerBonds]
  apply Finset.filter_true_of_mem
  intro b _
  refine ⟨Finset.mem_univ _, ?_⟩
  simp [axBonds]

/-- **A THIRD, INDEPENDENT PROOF of §7d's `bondLaplacianCov_not_zero_scalar_univ_empty`** — that one
went through the 32-bond even scatter and the GLOBAL `168 > 160` count; this one goes through the
48-bond layer family and the RELATIVE criterion, sharing neither the family nor the count. -/
theorem not_zero_scalar_univ_empty_relative (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ¬ (∀ v ∈ subspace156G (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ ell U,
        bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  refine not_zero_scalar_of_allowed _ _ ell U ?_
  rw [allowedLayerBonds_univ_empty, card_layerDir0Bonds]
  omega

/-! ## SHARPNESS: where this instrument saturates -/

/-- **No scatter family can exceed 64 bonds** — the codomain of `D_U^*` has dimension `64·dim 𝔰𝔲(2)`.
So the GLOBAL route can never run past `n = 63`, whatever family is used. -/
theorem scatter_card_le_64 (T : Finset (Bond witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hinj : LinearMap.ker (adjScatterT T U) = ⊥) : T.card ≤ 64 := by
  have hs := finrank_suTwo_pos
  have h := finrank_range_gradAdjoint_lower_of_scatter T U hinj
  have hle : Module.finrank ℝ (LinearMap.range (gradCovariantAdjointLM U))
      ≤ Module.finrank ℝ (PeriodicLatticeSite witnessL → SuTwo) := Submodule.finrank_le _
  rw [finrank_siteFn] at hle
  by_contra hc
  have hc' : 65 ≤ T.card := by omega
  have h65 : 65 * Module.finrank ℝ SuTwo ≤ T.card * Module.finrank ℝ SuTwo :=
    Nat.mul_le_mul_right _ hc'
  omega

/-- **The GLOBAL route provably cannot decide `c = 0` once `n ≥ 64`**: `dim ker D_U^*` is at least
`128·dim 𝔰𝔲(2) = (192−64)·dim 𝔰𝔲(2)` for EVERY `U`, so the §4 lower bound `(192−n)·dim 𝔰𝔲(2)` on
`dim V` cannot exceed it there. This is the exact saturation point of the dimension argument. -/
theorem global_route_saturates
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (n : ℕ) (hn : 64 ≤ n) :
    (192 - n) * Module.finrank ℝ SuTwo
      ≤ Module.finrank ℝ (LinearMap.ker (gradCovariantAdjointLM U)) := by
  have h := finrank_ker_gradAdjoint_lower U
  have hle : (192 - n) * Module.finrank ℝ SuTwo ≤ 128 * Module.finrank ℝ SuTwo :=
    Nat.mul_le_mul_right _ (by omega)
  omega

noncomputable def sumSiteLM : (PeriodicLatticeSite witnessL → SuTwo) →ₗ[ℝ] SuTwo where
  toFun F := ∑ y : PeriodicLatticeSite witnessL, F y
  map_add' F G := by simp [Finset.sum_add_distrib]
  map_smul' c F := by simp [Finset.smul_sum]

theorem sumSiteLM_surjective : Function.Surjective sumSiteLM := by
  intro X
  refine ⟨fun y => if y = witnessY then X else 0, ?_⟩
  show ∑ y : PeriodicLatticeSite witnessL, (if y = witnessY then X else 0) = X
  simp

theorem finrank_ker_sumSiteLM :
    Module.finrank ℝ (LinearMap.ker sumSiteLM) + Module.finrank ℝ SuTwo
      = 64 * Module.finrank ℝ SuTwo := by
  have hrn := LinearMap.finrank_range_add_finrank_ker sumSiteLM
  rw [finrank_siteFn] at hrn
  have hr : LinearMap.range sumSiteLM = ⊤ := LinearMap.range_eq_top.mpr sumSiteLM_surjective
  rw [hr, finrank_top] at hrn
  omega

/-- **The covariant divergence at a FLAT background telescopes to zero.** -/
theorem sum_gradAdjoint_trivialU (A : Bond witnessL → SuTwo) :
    sumSiteLM (gradCovariantAdjointLM (trivialU witnessL) A) = 0 := by
  show ∑ y : PeriodicLatticeSite witnessL,
    gradCovariantAdjointValue (trivialU witnessL) A y = 0
  have hU : ∀ b : Bond witnessL, ((trivialU witnessL) b)⁻¹
      = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
    intro b; show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = 1; simp
  simp only [gradCovariantAdjointValue, hU, RMap_one, LinearMap.id_coe, id_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro μ _
  rw [Finset.sum_sub_distrib]
  have hre : ∑ y : PeriodicLatticeSite witnessL, A (periodicLatticeShiftBack y μ, μ)
      = ∑ y : PeriodicLatticeSite witnessL, A (y, μ) :=
    Fintype.sum_equiv
      (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftEquiv
        (L := witnessL) μ).symm _ _ (fun _ => rfl)
  rw [hre, sub_self]

/-- **THE CEILING: at a flat background no scatter family can exceed 63 bonds.** The maximum forest
on 64 sites is a spanning tree, `63` edges; the 48-bond layer family used above is within 15 of that
ceiling, and `64` is unreachable. -/
theorem scatter_card_le_63_trivialU (T : Finset (Bond witnessL))
    (hinj : LinearMap.ker (adjScatterT T (trivialU witnessL)) = ⊥) : T.card ≤ 63 := by
  have hs := finrank_suTwo_pos
  have h := finrank_range_gradAdjoint_lower_of_scatter T (trivialU witnessL) hinj
  have hsub : LinearMap.range (gradCovariantAdjointLM (trivialU witnessL))
      ≤ LinearMap.ker sumSiteLM := by
    rintro x ⟨A, rfl⟩
    rw [LinearMap.mem_ker]
    exact sum_gradAdjoint_trivialU A
  have hmono := Submodule.finrank_mono hsub
  have hk := finrank_ker_sumSiteLM
  by_contra hc
  have hc' : 64 ≤ T.card := by omega
  have h64 : 64 * Module.finrank ℝ SuTwo ≤ T.card * Module.finrank ℝ SuTwo :=
    Nat.mul_le_mul_right _ hc'
  omega

/-! ## MUST-NOT-FIRE CONTROLS -/

/-- At `Λ := ∅` the conclusion is FALSE: the subspace is `⊥`, so `D_U D_U^*` IS `c·id` on it for
every `c`. Any criterion that fired there would be refuting a theorem. -/
theorem scalar_holds_at_lambda_empty (S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ) :
    ∀ v ∈ subspace156G (∅ : Finset (PeriodicLatticeSite witnessL)) S' ell U,
      bondLaplacianCovLM U v = c • v := by
  intro v hv
  have hv0 : v = 0 := by
    funext b
    exact hv.1.1 b (Finset.notMem_empty b.1)
  rw [hv0, map_zero, smul_zero]

/-- …and the relative criterion is refuted there: NO layer bond survives `Λ = ∅`. -/
theorem allowedLayerBonds_lambda_empty (S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    allowedLayerBonds (∅ : Finset (PeriodicLatticeSite witnessL)) S' ell = ∅ := by
  simp [allowedLayerBonds]

theorem allowedHyp_fails_at_lambda_empty (S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    ¬ (24 < (allowedLayerBonds (∅ : Finset (PeriodicLatticeSite witnessL)) S' ell).card) := by
  rw [allowedLayerBonds_lambda_empty]
  simp

/-- …and so is the global criterion (`192 + 0 + 24 < 48` is false). -/
theorem globalHyp_fails_at_lambda_empty (ell : ℕ) :
    ¬ ((outsideBonds (∅ : Finset (PeriodicLatticeSite witnessL))).card
        + (axBonds ∅ ell).card + 24 < layerDir0Bonds.card) := by
  rw [card_outsideBonds_empty, card_layerDir0Bonds]
  simp [axBonds]

/-! ## §DEGEN records and the non-flat instance -/

/-- At `ell = 0` clause 2 is vacuous, so MORE layer bonds survive (`47`, only `(witnessY,0)` lost to
`Λ`). Recorded so no reader treats a small-`ell` instance as evidence that clause 2 constrains
anything. -/
theorem card_allowedLayerBonds_ell_zero :
    (allowedLayerBonds (Finset.univ.erase witnessY) {witnessY} 0).card = 47 := by decide

/-- The headline INSTANTIATED at the tree's own NON-FLAT background `CovariantOperators.witnessU`. -/
theorem bondLaplacianCov_not_scalar_nondegenerate_witnessU (c : ℝ) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll
        AdalyFormal.Balaban.CovariantOperators.witnessU,
      bondLaplacianCovLM AdalyFormal.Balaban.CovariantOperators.witnessU v = c • v) :=
  bondLaplacianCov_not_scalar_nondegenerate _ c

/-! ## §DEDUP — the two locus clauses OVERLAP at the §5 point (verified here, not taken on report) -/

/-- **VERIFIED INDEPENDENTLY BY `decide`**: every bond `Λ = univ.erase witnessY` forbids is ALREADY
forbidden by `Ax witnessY`. `outsideBonds` filters on `b.1 ∉ Λ`, so it is exactly the three bonds
based at `witnessY = (0,0,0)`; `AxialContour.lean`'s own §4 docstring decomposes
`Ax witnessY witnessEll` as `1` trunk bond in direction `2` at `(0,0,0)`, `2` branch bonds in
direction `1` at `(0,0,0)` and `(0,0,1)`, and `4` leaf bonds in direction `0` at `(0,x₁,x₂)` — so all
three origin bonds are in it. -/
theorem outsideBonds_subset_axBonds_nondegenerate :
    outsideBonds (Finset.univ.erase witnessY) ⊆ axBonds {witnessY} witnessEll := by decide

theorem card_union_nondegenerate :
    (outsideBonds (Finset.univ.erase witnessY) ∪ axBonds {witnessY} witnessEll).card = 7 := by
  decide

/-- The MUST-NOT-FIRE companion: the inclusion is a fact about THIS parameter point, not a general
identity. At `Λ := ∅` it FAILS (all 192 bonds are outside, only 7 are axial). -/
theorem outsideBonds_not_subset_axBonds_lambda_empty :
    ¬ (outsideBonds (∅ : Finset (PeriodicLatticeSite witnessL))
        ⊆ axBonds {witnessY} witnessEll) := by decide

/-! ### the DEDUPLICATED clause map: ONE restriction onto the UNION, not two -/

abbrev ClauseCodU (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) : Type :=
  ({b : Bond witnessL // b ∈ outsideBonds Lambda ∪ axBonds S' ell} → SuTwo) ×
    (CoarseBond witnessL witnessEll → SuTwo)

noncomputable def clauseMapUnion (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (Bond witnessL → SuTwo) →ₗ[ℝ] ClauseCodU Lambda S' ell :=
  (restrictBonds (outsideBonds Lambda ∪ axBonds S' ell)).prod (Q1Real U)

theorem locusW_eq_ker_union (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    locusW Lambda S' ell
      = LinearMap.ker (restrictBonds (outsideBonds Lambda ∪ axBonds S' ell)) := by
  ext A
  rw [mem_ker_restrictBonds]
  constructor
  · rintro ⟨h1, h2⟩ b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact h1 b (mem_outsideBonds.mp hb)
    · obtain ⟨y, hy, hb'⟩ := mem_axBonds.mp hb
      exact h2 y hy b hb'
  · intro h
    refine ⟨?_, ?_⟩
    · intro b hb
      exact h b (Finset.mem_union_left _ (mem_outsideBonds.mpr hb))
    · intro y hy b hb
      exact h b (Finset.mem_union_right _ (mem_axBonds.mpr ⟨y, hy, hb⟩))

theorem ker_clauseMapUnion (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (clauseMapUnion Lambda S' ell U) = subspace156G Lambda S' ell U := by
  unfold clauseMapUnion
  rw [LinearMap.ker_prod, ← locusW_eq_ker_union, subspace156G_eq_inf]
  rfl

theorem finrank_clauseCodU (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    Module.finrank ℝ (ClauseCodU Lambda S' ell) =
      ((outsideBonds Lambda ∪ axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype (R := ℝ),
    Module.finrank_pi_fintype (R := ℝ)]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe, card_coarseBond]
  ring

/-- **THE DEDUPLICATED RANK–NULLITY BOUND** — the two locus clauses are counted ONCE on their
overlap. Strictly stronger than `finrank_subspace156G_lower` whenever they intersect, identical when
they do not. -/
theorem finrank_subspace156G_lower_union (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo ≤
      ((outsideBonds Lambda ∪ axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo
        + Module.finrank ℝ (subspace156G Lambda S' ell U) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (clauseMapUnion Lambda S' ell U)
  rw [ker_clauseMapUnion, finrank_bondFn] at hrn
  have hle : Module.finrank ℝ (LinearMap.range (clauseMapUnion Lambda S' ell U)) ≤
      Module.finrank ℝ (ClauseCodU Lambda S' ell) := Submodule.finrank_le _
  rw [finrank_clauseCodU] at hle
  omega

/-- The same on the `BFL2` carrier, by the same `bfl2Equiv` precomposition §2 uses. -/
noncomputable def clauseMapUnionBFL2 (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →ₗ[ℝ] ClauseCodU Lambda S' ell :=
  clauseMapUnion Lambda S' ell U ∘ₗ (bfl2Equiv (Lat := witnessL)).toLinearMap

theorem ker_clauseMapUnionBFL2 (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    LinearMap.ker (clauseMapUnionBFL2 Lambda S' ell U) = subspace156BFL2 Lambda S' ell U := by
  unfold clauseMapUnionBFL2 subspace156BFL2
  rw [LinearMap.ker_comp, ker_clauseMapUnion]

theorem finrank_subspace156BFL2_lower_union (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    192 * Module.finrank ℝ SuTwo ≤
      ((outsideBonds Lambda ∪ axBonds S' ell).card + 24) * Module.finrank ℝ SuTwo
        + Module.finrank ℝ (subspace156BFL2 Lambda S' ell U) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (clauseMapUnionBFL2 Lambda S' ell U)
  rw [ker_clauseMapUnionBFL2, finrank_bfl2] at hrn
  have hle : Module.finrank ℝ (LinearMap.range (clauseMapUnionBFL2 Lambda S' ell U)) ≤
      Module.finrank ℝ (ClauseCodU Lambda S' ell) := Submodule.finrank_le _
  rw [finrank_clauseCodU] at hle
  omega

/-- **`2 ≤ dim V` under the DEDUPLICATED cardinality hypothesis** — strictly weaker than §4's,
because the union card never exceeds the sum. -/
theorem two_le_finrank_subspace156BFL2_union (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcard : (outsideBonds Lambda ∪ axBonds S' ell).card + 26 ≤ 192) :
    2 ≤ Module.finrank ℝ (subspace156BFL2 Lambda S' ell U) := by
  have hs := finrank_suTwo_pos
  have hlow := finrank_subspace156BFL2_lower_union Lambda S' ell U
  set s := Module.finrank ℝ SuTwo with hsdef
  set n := (outsideBonds Lambda ∪ axBonds S' ell).card + 24 with hndef
  set F := Module.finrank ℝ (subspace156BFL2 Lambda S' ell U) with hFdef
  have hn2 : n + 2 ≤ 192 := by omega
  have hmul : (n + 2) * s ≤ 192 * s := Nat.mul_le_mul_right s hn2
  have h1 : n * s + 2 * s ≤ n * s + F := by
    calc n * s + 2 * s = (n + 2) * s := by ring
      _ ≤ 192 * s := hmul
      _ ≤ n * s + F := hlow
  have h2 : 2 * s ≤ F := Nat.le_of_add_le_add_left h1
  omega

/-- **`161 · dim 𝔰𝔲(2) ≤ dim V` at the §5 non-degenerate point** — the sharp count, replacing `158`.
`3 + 7 → 7`: the three `Λ`-forbidden bonds were being counted twice. -/
theorem finrank_subspace156G_nondegenerate_sharp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    161 * Module.finrank ℝ SuTwo
      ≤ Module.finrank ℝ (subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U) := by
  have h := finrank_subspace156G_lower_union (Finset.univ.erase witnessY) {witnessY} witnessEll U
  rw [card_union_nondegenerate] at h
  omega

/-- **`c = 0` AT THE §5 POINT FROM THE DEDUP ALONE** — `161 · s > 160 · s`, against the ALREADY-FILED
32-bond kernel bound `finrank_ker_gradAdjoint_upper`. No 48-bond scatter needed. -/
theorem not_zero_scalar_nondegenerate_dedup
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U,
        bondLaplacianCovLM U v = (0 : ℝ) • v) := by
  intro hscal
  have hs := finrank_suTwo_pos
  have hle : subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U
      ≤ LinearMap.ker (gradCovariantAdjointLM U) := by
    rw [← ker_bondLaplacian_eq_ker_gradAdjoint]
    intro v hv
    rw [LinearMap.mem_ker]
    have h := hscal v hv
    rwa [zero_smul] at h
  have hmono := Submodule.finrank_mono hle
  have hupper := finrank_ker_gradAdjoint_upper U
  have hlow := finrank_subspace156G_nondegenerate_sharp U
  omega

/-! ## §GENERAL — the strongest statements reached, general in `Λ`, `S'`, `ell`, `U`, `c` -/

/-- §7b's dimension argument, parameterized by whatever lower bound on `dim V` is available.
`bondLaplacianCov_not_nonzero_scalar_on_subspace156G` (§7b) is the `n := |outside| + |ax| + 24`
instance of exactly this; only the numeric input differs. -/
theorem bondLaplacianCov_not_nonzero_scalar_of_dim
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (n : ℕ)
    (hlow : 192 * Module.finrank ℝ SuTwo
      ≤ n * Module.finrank ℝ SuTwo + Module.finrank ℝ (subspace156G Lambda S' ell U))
    (hn : n + 64 ≤ 191) (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = c • v) := by
  intro hscal
  have hs := finrank_suTwo_pos
  set s := Module.finrank ℝ SuTwo with hsdef
  have hdisj : subspace156G Lambda S' ell U ⊓ LinearMap.ker (bondLaplacianCovLM U) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨hV, hK⟩ := hv
    have h1 : bondLaplacianCovLM U v = c • v := hscal v hV
    have h2 : bondLaplacianCovLM U v = 0 := by
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hK; exact hK
    have h3 : c • v = 0 := by rw [← h1, h2]
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h hc
    · exact (Submodule.mem_bot ℝ).mpr h
  have hsum : Module.finrank ℝ (subspace156G Lambda S' ell U)
      + Module.finrank ℝ (LinearMap.ker (bondLaplacianCovLM U)) ≤ 192 * s := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq
      (subspace156G Lambda S' ell U) (LinearMap.ker (bondLaplacianCovLM U))
    rw [hdisj, finrank_bot] at he
    have hle : Module.finrank ℝ
        ((subspace156G Lambda S' ell U ⊔ LinearMap.ker (bondLaplacianCovLM U) :
          Submodule ℝ (Bond witnessL → SuTwo))) ≤
        Module.finrank ℝ (Bond witnessL → SuTwo) := Submodule.finrank_le _
    rw [finrank_bondFn] at hle
    omega
  have hker := finrank_ker_bondLaplacian_lower U
  have hmul : (n + 64) * s ≤ 191 * s := Nat.mul_le_mul_right s hn
  have hexp : (n + 64) * s = n * s + 64 * s := by ring
  omega

/-! ### the deduplicated general theorems -/

theorem not_zero_scalar_of_scatter_union
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (T : Finset (Bond witnessL)) (hinj : LinearMap.ker (adjScatterT T U) = ⊥)
    (hcard : (outsideBonds Lambda ∪ axBonds S' ell).card + 24 < T.card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = (0 : ℝ) • v) :=
  not_zero_scalar_of_scatter_of_dim Lambda S' ell U T _
    (finrank_subspace156G_lower_union Lambda S' ell U) hinj hcard

theorem bondLaplacianCov_not_nonzero_scalar_union
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcard : (outsideBonds Lambda ∪ axBonds S' ell).card + 24 + 64 ≤ 191) (c : ℝ) (hc : c ≠ 0) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = c • v) :=
  bondLaplacianCov_not_nonzero_scalar_of_dim Lambda S' ell U _
    (finrank_subspace156G_lower_union Lambda S' ell U) hcard c hc

/-- **THE SINGLE-HYPOTHESIS GENERAL THEOREM: `D_U D_U^*` is not `c·id` on the admissible subspace,
for EVERY `Λ`, `S'`, `ell`, `U` and EVERY real `c`, whenever the two locus clauses jointly forbid at
most 23 bonds.** `c ≠ 0` needs only `≤ 103`; `c = 0` is what forces `≤ 23`, via the 48-bond family.
Decidable for any concrete `Λ`, `S'`, `ell`. -/
theorem bondLaplacianCov_not_scalar_of_card_union
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ)
    (hcard : (outsideBonds Lambda ∪ axBonds S' ell).card ≤ 23) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine not_zero_scalar_of_scatter_union Lambda S' ell U layerDir0Bonds
      (adjScatterT_layer_ker_eq_bot U) ?_
    rw [card_layerDir0Bonds]; omega
  · exact bondLaplacianCov_not_nonzero_scalar_union Lambda S' ell U (by omega) c hc

/-- **THE WIDEST GENERAL THEOREM.** The `c = 0` hypothesis is now purely LOCAL — it does not bound
the total number of forbidden bonds at all, only how many of the 48 layer bonds they hit. It holds
with up to `144` forbidden bonds provided ≥ 25 layer bonds survive. -/
theorem bondLaplacianCov_not_scalar_general_union
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ)
    (hnz : (outsideBonds Lambda ∪ axBonds S' ell).card + 24 + 64 ≤ 191)
    (hallow : 24 < (allowedLayerBonds Lambda S' ell).card) :
    ¬ (∀ v ∈ subspace156G Lambda S' ell U, bondLaplacianCovLM U v = c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact not_zero_scalar_of_allowed Lambda S' ell U hallow
  · exact bondLaplacianCov_not_nonzero_scalar_union Lambda S' ell U hnz c hc

/-- The §5 non-degenerate point is the `|union| = 7 ≤ 23` instance of the general theorem — a FOURTH
independent derivation of it, now with no reference to the parameter point in the proof. -/
theorem bondLaplacianCov_not_scalar_nondegenerate_from_general
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (c : ℝ) :
    ¬ (∀ v ∈ subspace156G (Finset.univ.erase witnessY) {witnessY} witnessEll U,
        bondLaplacianCovLM U v = c • v) := by
  refine bondLaplacianCov_not_scalar_of_card_union _ _ witnessEll U c ?_
  rw [card_union_nondegenerate]
  omega

/-! ### exactly where the DIMENSION route saturates (deliverable 3) -/

/-- **The `c = 0` GLOBAL comparison provably cannot run once the union forbids 40 bonds.**
`dim ker D_U^* ≥ 128·dim 𝔰𝔲(2)` for EVERY `U` (rank–nullity, `64` sites), while the deduplicated
lower bound on `dim V` is `(168 − m)·dim 𝔰𝔲(2)`; at `m ≥ 40` the latter no longer exceeds the former,
whatever scatter family is used. So the §4 cardinality hypothesis (`m ≤ 166`) is NOT reachable by any
argument of this shape — the gap between `40` and `166` is not a missing lemma, it is the ceiling of
the method. -/
theorem global_route_saturates_union
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (m : ℕ) (hm : 40 ≤ m) :
    (192 - (m + 24)) * Module.finrank ℝ SuTwo
      ≤ Module.finrank ℝ (LinearMap.ker (gradCovariantAdjointLM U)) := by
  have h := finrank_ker_gradAdjoint_lower U
  have hle : (192 - (m + 24)) * Module.finrank ℝ SuTwo ≤ 128 * Module.finrank ℝ SuTwo :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **…and the `c ≠ 0` comparison cannot run once the union forbids 104.** `§7b` needs
`dim V + dim ker(D_U D_U^*) > 192·dim 𝔰𝔲(2)`; the available bounds are `(168−m)` and `128`, and
`(168−m) + 128 ≤ 192` exactly when `m ≥ 104`. Stated as the arithmetic it is: the two bounds do not
combine to a contradiction there. -/
theorem nonzero_route_saturates_union (m : ℕ) (hm : 104 ≤ m) :
    (192 - (m + 24)) * Module.finrank ℝ SuTwo + 128 * Module.finrank ℝ SuTwo
      ≤ 192 * Module.finrank ℝ SuTwo := by
  have hle : (192 - (m + 24)) * Module.finrank ℝ SuTwo ≤ 64 * Module.finrank ℝ SuTwo :=
    Nat.mul_le_mul_right _ (by omega)
  omega


#print axioms scatterT
#print axioms scatterT_apply_mem
#print axioms scatterT_apply_notMem
#print axioms adjScatterT
#print axioms scatterEven_eq
#print axioms adjScatter_eq
#print axioms layerDir0Bonds
#print axioms mem_layerDir0Bonds
#print axioms card_layerDir0Bonds
#print axioms genDivValue
#print axioms genDivValue_eq
#print axioms shiftBack_coord0
#print axioms scatterTriangular_eq_zero
#print axioms shiftBack_coord0_lt
#print axioms scatterLayer_eq_zero
#print axioms adjScatterT_layer_ker_eq_bot
#print axioms scatterLayer_eq_zero_zeroTransport
#print axioms finrank_scatterT_domain
#print axioms ker_scatterT_eq_bot
#print axioms finrank_range_scatterT
#print axioms finrank_range_gradAdjoint_lower_of_scatter
#print axioms finrank_ker_gradAdjoint_upper_of_scatter
#print axioms not_zero_scalar_of_scatter_of_dim
#print axioms not_zero_scalar_of_scatter_global
#print axioms locusW
#print axioms subspace156G_eq_inf
#print axioms finrank_coarseFn
#print axioms finrank_ker_q1Real_lower
#print axioms finrank_locusW_le
#print axioms range_scatterT_le_locusW
#print axioms range_scatterT_inf_ker_eq_bot
#print axioms not_zero_scalar_of_transverse
#print axioms not_zero_scalar_of_scatter_relative
#print axioms extZero
#print axioms scatterT_extZero
#print axioms ker_adjScatterT_mono
#print axioms allowedLayerBonds
#print axioms allowedLayerBonds_subset
#print axioms mem_allowedLayerBonds
#print axioms ker_adjScatterT_allowed
#print axioms not_zero_scalar_of_allowed
#print axioms card_allowedLayerBonds_nondegenerate
#print axioms not_zero_scalar_nondegenerate_global
#print axioms not_zero_scalar_nondegenerate_relative
#print axioms bondLaplacianCov_not_scalar_nondegenerate
#print axioms bondLaplacianCov_not_scalar_general
#print axioms finrank_range_gradAdjoint_lower48
#print axioms finrank_ker_gradAdjoint_upper48
#print axioms allowedLayerBonds_univ_empty
#print axioms not_zero_scalar_univ_empty_relative
#print axioms scatter_card_le_64
#print axioms global_route_saturates
#print axioms sumSiteLM
#print axioms sumSiteLM_surjective
#print axioms finrank_ker_sumSiteLM
#print axioms sum_gradAdjoint_trivialU
#print axioms scatter_card_le_63_trivialU
#print axioms scalar_holds_at_lambda_empty
#print axioms allowedLayerBonds_lambda_empty
#print axioms allowedHyp_fails_at_lambda_empty
#print axioms globalHyp_fails_at_lambda_empty
#print axioms card_allowedLayerBonds_ell_zero
#print axioms bondLaplacianCov_not_scalar_nondegenerate_witnessU
#print axioms outsideBonds_subset_axBonds_nondegenerate
#print axioms card_union_nondegenerate
#print axioms outsideBonds_not_subset_axBonds_lambda_empty
#print axioms ClauseCodU
#print axioms clauseMapUnion
#print axioms locusW_eq_ker_union
#print axioms ker_clauseMapUnion
#print axioms finrank_clauseCodU
#print axioms finrank_subspace156G_lower_union
#print axioms clauseMapUnionBFL2
#print axioms ker_clauseMapUnionBFL2
#print axioms finrank_subspace156BFL2_lower_union
#print axioms two_le_finrank_subspace156BFL2_union
#print axioms finrank_subspace156G_nondegenerate_sharp
#print axioms not_zero_scalar_nondegenerate_dedup
#print axioms bondLaplacianCov_not_nonzero_scalar_of_dim
#print axioms not_zero_scalar_of_scatter_union
#print axioms bondLaplacianCov_not_nonzero_scalar_union
#print axioms bondLaplacianCov_not_scalar_of_card_union
#print axioms bondLaplacianCov_not_scalar_general_union
#print axioms bondLaplacianCov_not_scalar_nondegenerate_from_general
#print axioms global_route_saturates_union
#print axioms nonzero_route_saturates_union

/-! ## §MUSTFIRE — the `x₀ ≤ 2` restriction is LOAD-BEARING, proved by counterexample

Dropping it (taking all 64 direction-`0` bonds) makes `adjScatterT_layer_ker_eq_bot` FALSE, with an
explicit nonzero kernel element: a field CONSTANT along every direction-`0` line has vanishing
covariant divergence at a flat background, because each line closes into a cycle. This is the
must-FIRE control for the layer hypothesis — not "I can see it would fail", but an exhibited failure.
It is also consistent with `scatter_card_le_63_trivialU`: `64 > 63`, so no 64-bond family can be
scatter-injective at `trivialU`, and here is the witness. -/

def fullDir0Bonds : Finset (Bond witnessL) :=
  Finset.univ.filter (fun b => b.2 = (0 : Fin 3))

theorem mem_fullDir0Bonds {b : Bond witnessL} : b ∈ fullDir0Bonds ↔ b.2 = (0 : Fin 3) := by
  simp [fullDir0Bonds]

theorem card_fullDir0Bonds : fullDir0Bonds.card = 64 := by decide

theorem layerDir0Bonds_subset_full : layerDir0Bonds ⊆ fullDir0Bonds := by decide

noncomputable def constDir0 : {b : Bond witnessL // b ∈ fullDir0Bonds} → SuTwo :=
  fun _ => suTwoWitness

theorem scatterT_full_constDir0 (b : Bond witnessL) :
    scatterT fullDir0Bonds constDir0 b = if b.2 = (0 : Fin 3) then suTwoWitness else 0 := by
  by_cases h : b ∈ fullDir0Bonds
  · rw [scatterT_apply_mem _ h, if_pos (mem_fullDir0Bonds.mp h)]; rfl
  · rw [scatterT_apply_notMem _ h, if_neg (fun hc => h (mem_fullDir0Bonds.mpr hc))]

theorem adjScatter_full_constDir0_eq_zero :
    adjScatterT fullDir0Bonds (trivialU witnessL) constDir0 = 0 := by
  funext y
  show gradCovariantAdjointValue (trivialU witnessL) (scatterT fullDir0Bonds constDir0) y = 0
  have hU : ∀ b : Bond witnessL, ((trivialU witnessL) b)⁻¹
      = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
    intro b; show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = 1; simp
  unfold gradCovariantAdjointValue
  simp only [hU, RMap_one, LinearMap.id_coe, id_eq]
  rw [Fin.sum_univ_three]
  simp [scatterT_full_constDir0]

/-- **THE MUST-FIRE CONTROL, FIRED.** -/
theorem adjScatterT_full_ker_ne_bot :
    LinearMap.ker (adjScatterT fullDir0Bonds (trivialU witnessL)) ≠ ⊥ := by
  intro h
  have hmem : constDir0 ∈ LinearMap.ker (adjScatterT fullDir0Bonds (trivialU witnessL)) :=
    LinearMap.mem_ker.mpr adjScatter_full_constDir0_eq_zero
  rw [h, Submodule.mem_bot] at hmem
  have hv := congrFun hmem ⟨(witnessY, (0 : Fin 3)), mem_fullDir0Bonds.mpr rfl⟩
  exact suTwoWitness_ne_zero hv


#print axioms fullDir0Bonds
#print axioms mem_fullDir0Bonds
#print axioms card_fullDir0Bonds
#print axioms layerDir0Bonds_subset_full
#print axioms constDir0
#print axioms scatterT_full_constDir0
#print axioms adjScatter_full_constDir0_eq_zero
#print axioms adjScatterT_full_ker_ne_bot

end AdalyFormal.Balaban.NonDegenerateInstances
