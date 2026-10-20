/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Coercivity
import AdalyFormal.Balaban.LineIntegralAveraging

set_option autoImplicit false

/-!
# `AnchoredVFull` — CMP99b p.428's admissible subspace with ALL THREE conditions

## THE DEFECT THIS FILE REPAIRS (statement-level, on the goal itself)

`Spine.coerc_u_main` pins `cohyp.V = Balaban.Anchoring.anchoredVInter (Lat := Lat) ell`. Read from
the `def` (`Balaban/Coercivity.lean:479` → `Balaban/AdmissibleSubspace.lean:443`), that subspace's
carrier is

```lean
{B | ∀ y, y ∈ CoarseLattice L ell → ∀ x, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, B b = 0}
```

— the **axial/staircase gauge condition ALONE**. CMP99b printed p.428, read at 600 dpi by this lane
(`compute/anchored_v_full/p600-40.png`, sha256
`1f10b132cf62b75250c0ccd19e37c796e16bbbf958d37f66f623a4d14ded6883`; printed number `428` visible in
`crop_p428_head.png`, so printed = pdf + 388), immediately below (3.156), VERBATIM:

> This form is considered on the subspace `{B: B = 0 on Λᶜ, B = 0 on ⋃_{y∈Λ'} Ax(y), Q₁B = 0}`. We
> can parametrize this subspace in the same way as in [4] (2.154-2.155), using part of the variables
> `B`, which we denote by `B̃`.

**THREE** conditions. `anchoredVInter` carries ONE. This module builds the full object.

## THE THREE CLAUSES, AND HOW EACH IS ENCODED HERE

1. **`B = 0` on `Λᶜ`.** `lambdaSupported Λbonds` (§1). Bałaban's `Λ` is a region of the *unit
   lattice* ("a union of big blocks", p.427 §E), i.e. a set of SITES; the induced BOND set is not
   pinned by the page (base-in-`Λ` vs both-endpoints-in-`Λ` is exactly the quantifier-weakening
   class S83 warns about), so this module takes the **bond set as a parameter** and does NOT invent
   the site→bond reduction. Named residual: `[LAMBDA-BOND-SET]`, §8.
   The tree's carrier is the FULL periodic torus (`Λ = everything`), where this clause is vacuous
   (`lambdaSupported_univ`), which is why `anchoredVInter` could omit it without being caught.
2. **`B = 0` on `⋃_{y∈Λ'} Ax(y)`.** `admissibleSubspaceInter L ell`, imported unchanged (LAW-19).
   `Ax(y) = ⋃_{x∈B(y)} Γ_{y,x}`: CMP99b never defines `Ax(y)` (2 occurrences in the whole paper,
   both on p.428, both uses), but CMP96 (=[4]) p.249 writes the SAME subspace as
   `QB = 0, B(Γ_{y,x}) = 0 for x ∈ B(y)` (glyph-verified at 600 dpi, `compute/q1_adjudication/
   RULING.md` §1h). Recorded as a READING supported by the parallel passage, not a verbatim
   definition.
3. **`Q₁B = 0`.** `kerQOne L ell` (§2), a one-to-one transcription of the clause
   (`∀ c, (Q₁B)(c) = 0`) proved EQUAL to `LinearMap.ker (lineCoarseRestrictLM L ell)`
   (`kerQOne_eq_ker`), built on the
   **FAITHFUL** line-integral average `LineIntegralAveraging.lineCoarseRestrict` (CMP95
   (1.11)/(1.18)) — NOT `LatticeOperators.coarseRestrict`, which drops the line integral and is a
   convicted operator (`LineIntegralAveraging.coarseRestrict_const_witness`: it returns `1/2` on the
   constant field `1` where the faithful operator returns `1`).

## IS THE `Q₁` CLAUSE `U`-DEPENDENT? — YES IN THE SOURCE; NOT EXPRESSIBLE AT THIS CARRIER

CMP99b p.393 (3.15)/(3.18)/(3.19) give the one-step averaging template as `Q(V)` with
`R(V(Γ_{y,x}))` **adjoint transport** (600 dpi, `compute/q1_adjudication/RULING.md` §1a/§1b, whose
p.427/p.428 renders this lane reproduced byte-identically). So Bałaban's `Q₁` genuinely depends on
the background. **But** `R(V(Γ))` is the adjoint action of `SU(2)` on `𝔰𝔲(2) ≅ ℝ³`, and
`coerc_u_main` pins `cohyp.V : Submodule ℝ (Anchoring.AnchoredBondSpace Lat)` with
`AnchoredBondSpace Lat = EuclideanSpace ℝ (Bond Lat)` — a **one-dimensional real fibre per bond**,
with no `Ad`-action to carry. Hence:

* at the carrier the goal statement currently uses, the faithful `Q₁` **is** the flat
  `lineCoarseRestrict`, and the flat clause built here is the correct repair;
* the genuinely `U`-dependent clause already exists in this tree, on the su(2) carrier:
  `CoercivitySupply.MemKerQ ell U A := ∀ c, lineCoarseRestrictCov U ell A c = 0`, packaged as
  `CoercivitySupply.Admissible ell U A := AxialGauge ell A ∧ MemKerQ ell U A`. It is NOT rebuilt
  here (LAW-19);
* **REPORTED, NOT REPAIRED (out of write scope):** `CoercivityHypothesis.V` is a single
  `Submodule ℝ H`, *not* a function of `Uconfig`. A faithful `U`-dependent admissible subspace
  therefore does not fit that field's TYPE. That is a second, independent statement-level defect on
  the goal, one level above this one. See §8.

## DENOTATION AUDIT — WHICH LEVEL, AND WHAT THIS OBJECT DOES *NOT* SAY

The two non-vacuous clauses are at the **SAME** level, and this module uses ONE `ell` for both.
That is deliberate and source-checked: `Λ'` on p.428 indexes big blocks OF THE UNIT LATTICE
(`B(c) = {b : b₋ ∈ B(c₋), b₊ ∈ B(c₊)}`), `Ax(y)` for `y ∈ Λ'` is a set of UNIT-lattice bonds, and
`Q₁` maps unit-lattice fields to `Λ'`. So both clauses describe the single unit→`Λ'` step.
It converges with `CoercivitySupply.Admissible ell U A := AxialGauge ell A ∧ MemKerQ ell U A`,
which also uses one `ell` for both — two independently-built objects agreeing.

**`[CSTAR-LEVEL-MISMATCH]` is a DIFFERENT arrow and is untouched here.** The `Q` inside
`(QG₁Q*)⁻¹` — i.e. inside `Δ_k` itself — is the fine→unit composite, one or more levels BELOW `Q₁`
(`compute/q1_adjudication/RULING.md` §5a/§5b). This module constrains the domain; it says nothing
about `Δ_k`'s own level bookkeeping, and must not be read as fixing it.

**What the §5 witness does and does NOT certify.** `wConfig` satisfies the axial clause by
DISJOINT SUPPORT (it lives on direction-`2` bonds whose base has `(z 0).val % ell ≠ 0`, and no
staircase direction-`2` segment reaches those), not by any cancellation. That is what a nonzero
element must look like, but it means `anchoredVFull_ne_bot` certifies only `≠ ⊥` — NOT that the
subspace is large, and NOT anything about its dimension.

## WHAT IS PROVED HERE (all `sorry`-free; `#print axioms` after each block)

* `anchoredVFull_le_anchoredVInter` (§4): `anchoredVFull Lat ell ≤ anchoredVInter ell`,
  UNCONDITIONALLY (every `Lat`, every `ell`).
* `anchoredVFull_ne_bot` (§5): `≠ ⊥` under `2 ≤ ell` and `∀ μ, ell ∣ (Lat μ + 1)`, via the EXPLICIT
  witness `wConfig`. Load-bearing: `CoercivityHypothesis.V_ne_bot` is a mandatory field.
  *Hypothesis honesty:* the proof consumes only `hdvd 0` and `hdvd 2`, so the `∀ μ` form is stronger
  than the argument needs; it is kept because it is the tileability condition every consumer already
  carries (`coarseLattice_exists`, `coarseShift_mem_coarseLattice`), not because all three are used.
* **STRICT** inclusion (§6): `anchoredVFull_lt_anchoredVInter`, under `2 ≤ ell` and
  `ell ∣ (L 0 + 1)` ONLY (no other direction needed) — `strictConfig` is in `anchoredVInter ell` and
  NOT in `anchoredVFull ell`. Without this the repair could be cosmetic. `kerQOne_ne_top` is the
  companion control: the added clause is not `⊤`, so it genuinely removes vectors.
* the `ell ∈ {0,1}` degeneration (§7), and it is WORSE than the dispatch expected:
  `anchoredVInter 0 = anchoredVInter 1 = ⊤` (the known defect) but
  **`anchoredVFull 1 = ⊥`** and `anchoredVFull 0 = ⊤`. `ell = 1` is therefore a genuine
  OBSTRUCTION to stating the goal with the faithful domain: no `CoercivityHypothesis` can have
  `V = anchoredVFull 1`, because `V_ne_bot` is unsatisfiable there
  (`no_coercivityHypothesis_at_anchoredVFull_one`).

## DEGENERATE-INHABITATION ATTEMPTS, KEPT AS THEOREMS (dispatch requirement)

* `wConfig_one_eq_zero` — the §5 witness COLLAPSES to `0` at `ell = 1`, i.e. it does not
  accidentally survive at the degenerate scale where every alternative coincides.
* `window_sum_fails_without_dvd` — the load-bearing window-sum identity is FALSE at
  `(ell, N) = (2, 3)`, so the divisibility hypothesis in §5 is not decoration.
* `anchoredVFull_one_eq_bot` / `anchoredVFull_zero_eq_top` — the two failed inhabitations.
-/

namespace AdalyFormal.Balaban.AnchoredVFull

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (CoarseBond gradValue)
open AdalyFormal.Balaban.LineIntegralAveraging (lineIntegralValue lineCoarseRestrict
  lineCoarseRestrictLM)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq
  periodicLatticeShift_self)
open AdalyFormal.Balaban.KernelSubspace (blockOf_one_eq_singleton)
open AdalyFormal.Balaban.Anchoring (AnchoredBondSpace anchoredVInter)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — Small geometric facts (the two `ell`-degenerate blocks, and the empty segment) -/

/-- `axisSegment` with an empty sweep range is empty. -/
theorem axisSegment_self_empty (base : PeriodicLatticeSite L) (μ : Fin 3) (a : ℕ) :
    axisSegment base μ a a = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_axisSegment] at he
  obtain ⟨-, -, h1, h2⟩ := he
  omega

/-- **`Γ_{y,y} = ∅`** — the staircase from a site to itself has no bonds. -/
theorem staircasePath_self (y : PeriodicLatticeSite L) : staircasePath y y = ∅ := by
  unfold staircasePath
  rw [min_self, max_self, min_self, max_self, min_self, max_self]
  rw [axisSegment_self_empty, axisSegment_self_empty, axisSegment_self_empty]
  simp

/-- Every site is coarse at `ell = 1` (`n % 1 = 0`). Local three-line restatement; the same fact
already exists at `CoercivitySupply.mem_CoarseLattice_one`, `QOne.mem_CoarseLattice_one` and
`CovariantHjMinimizer.mem_CoarseLattice_one`, none of which is importable here without dragging in
the whole su(2) chain — disclosed duplication rather than a silent fourth copy. -/
theorem mem_coarseLattice_one (y : PeriodicLatticeSite L) : y ∈ CoarseLattice L 1 := by
  rw [mem_CoarseLattice]
  intro μ
  exact Nat.mod_one _

/-- **`B(y) = ∅` at `ell = 0`** — `y μ ≤ x μ < y μ + 0` is unsatisfiable. -/
theorem blockOf_zero_empty (y : PeriodicLatticeSite L) : blockOf y 0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_blockOf] at hx
  have := hx 0
  omega

#print axioms axisSegment_self_empty
#print axioms staircasePath_self
#print axioms mem_coarseLattice_one
#print axioms blockOf_zero_empty

/-! ## §1 — CLAUSE 1: `B = 0` on `Λᶜ` -/

/-- **`{B : B = 0 on Λᶜ}`**, with `Λ` given as an explicit BOND set. The site→bond reduction of
Bałaban's `Λ` ("a union of big blocks" of the unit lattice, p.427 §E) is deliberately NOT invented
here — see the module docstring, clause 1, and `[LAMBDA-BOND-SET]` in §8. -/
def lambdaSupported (Lambda : Finset (Bond L)) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ b : Bond L, b ∉ Lambda → B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by intro B1 B2 h1 h2 b hb; simp [h1 b hb, h2 b hb]
  smul_mem' := by intro c B h b hb; simp [h b hb]

theorem mem_lambdaSupported {Lambda : Finset (Bond L)} {B : Bond L → ℝ} :
    B ∈ lambdaSupported Lambda ↔ ∀ b : Bond L, b ∉ Lambda → B b = 0 := Iff.rfl

/-- On the FULL torus the `Λᶜ` clause is vacuous — the exact reason `anchoredVInter` could omit it
undetected on this carrier. -/
theorem lambdaSupported_univ : lambdaSupported (L := L) Finset.univ = ⊤ := by
  ext B
  simp [mem_lambdaSupported]

/-- **CONTROL — the `Λᶜ` clause has real content**, and can be FATAL: at `Λ = ∅` it is already `⊥`
on its own. So a consumer instantiating `anchoredVFullOn` at a small `Λ` must discharge non-vacuity
for that `Λ`; `anchoredVFull_ne_bot` (§5) covers only the full-torus case. -/
theorem lambdaSupported_empty : lambdaSupported (L := L) ∅ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro B hB
  funext b
  exact hB b (Finset.notMem_empty b)

#print axioms lambdaSupported
#print axioms lambdaSupported_univ
#print axioms lambdaSupported_empty

/-! ## §2 — CLAUSE 3: `Q₁B = 0`, over the FAITHFUL line-integral `Q` -/

/-- **`{B : Q₁B = 0}`, faithful.** Written as a one-to-one transcription of the source clause
(`Q₁B = 0` at every coarse bond), in the same style as `admissibleSubspaceInter`'s carrier, and
identified with the kernel of the FAITHFUL `LinearMap` by `kerQOne_eq_ker` below.
`LineIntegralAveraging.lineCoarseRestrict` is CMP95 (1.11)/(1.18) WITH its line integral
(`(1/ell⁴)·Σ_{x∈B(y)} B([x, x+ell·e_μ])`); `LatticeOperators.coarseRestrict` is the convicted
single-bond port and is NOT used. -/
noncomputable def kerQOne (L : PeriodicLatticeExtent) (ell : ℕ) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ c : CoarseBond L ell, lineCoarseRestrict ell B c = 0}
  zero_mem' := by
    intro c
    simp [lineCoarseRestrict, lineIntegralValue]
  add_mem' := by
    intro B1 B2 h1 h2 c
    rw [AdalyFormal.Balaban.LineIntegralAveraging.lineCoarseRestrict_add, h1 c, h2 c, add_zero]
  smul_mem' := by
    intro a B h c
    rw [AdalyFormal.Balaban.LineIntegralAveraging.lineCoarseRestrict_smul, h c, mul_zero]

theorem mem_kerQOne {ell : ℕ} {B : Bond L → ℝ} :
    B ∈ kerQOne L ell ↔ ∀ c : CoarseBond L ell, lineCoarseRestrict ell B c = 0 := Iff.rfl

/-- **The clause IS the kernel of the faithful operator** — so nothing about `kerQOne`'s explicit
carrier can drift from `lineCoarseRestrictLM`. -/
theorem kerQOne_eq_ker (ell : ℕ) :
    kerQOne L ell = LinearMap.ker (lineCoarseRestrictLM L ell) := by
  ext B
  rw [mem_kerQOne, LinearMap.mem_ker]
  constructor
  · intro h; exact funext fun c => h c
  · intro h c; exact congrFun h c

/-- `lineIntegralValue` written over `coarseShift` — the same term, `rfl`, so `coarseShift`'s
proved coordinate lemmas (LAW-19) apply to it. -/
theorem lineIntegralValue_eq_coarseShift (ell : ℕ) (A : Bond L → ℝ) (x : PeriodicLatticeSite L)
    (μ : Fin 3) :
    lineIntegralValue ell A x μ = ∑ j ∈ Finset.range ell, A (coarseShift x j μ, μ) := rfl

#print axioms kerQOne
#print axioms kerQOne_eq_ker
#print axioms lineIntegralValue_eq_coarseShift

/-! ## §3 — THE FULL SUBSPACE at the bare `Pi` carrier -/

/-- **CMP99b p.428's subspace, all three conditions.** -/
noncomputable def admissibleSubspaceFullOn (L : PeriodicLatticeExtent)
    (Lambda : Finset (Bond L)) (ell : ℕ) : Submodule ℝ (Bond L → ℝ) :=
  lambdaSupported Lambda ⊓ admissibleSubspaceInter L ell ⊓ kerQOne L ell

/-- The full-torus specialization (`Λ = everything`), which is the case the tree's carrier is. -/
noncomputable def admissibleSubspaceFull (L : PeriodicLatticeExtent) (ell : ℕ) :
    Submodule ℝ (Bond L → ℝ) :=
  admissibleSubspaceFullOn L Finset.univ ell

theorem mem_admissibleSubspaceFull {ell : ℕ} {B : Bond L → ℝ} :
    B ∈ admissibleSubspaceFull L ell ↔
      (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, B b = 0) ∧
      (∀ c : CoarseBond L ell, lineCoarseRestrict ell B c = 0) := by
  unfold admissibleSubspaceFull admissibleSubspaceFullOn
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_kerQOne, mem_admissibleSubspaceInter]
  constructor
  · rintro ⟨⟨-, hax⟩, hq⟩; exact ⟨hax, hq⟩
  · rintro ⟨hax, hq⟩
    refine ⟨⟨?_, hax⟩, hq⟩
    intro b hb
    exact absurd (Finset.mem_univ b) hb

theorem admissibleSubspaceFull_le_inter (ell : ℕ) :
    admissibleSubspaceFull L ell ≤ admissibleSubspaceInter L ell := by
  intro B hB
  rw [mem_admissibleSubspaceFull] at hB
  exact hB.1

#print axioms admissibleSubspaceFullOn
#print axioms mem_admissibleSubspaceFull
#print axioms admissibleSubspaceFull_le_inter

/-! ## §4 — TRANSPORT to the anchored Hilbert space, and RELATIONSHIP 1 (`≤`)

Same `Submodule.map` along the same `WithLp` linear equivalence `Anchoring.anchoredVInter` uses
(LAW-19); nothing new mathematically, so the transported object cannot drift from the bare one. -/

/-- **CMP99b p.428's subspace, transported to `AnchoredBondSpace`** — the object `coerc_u_main`'s
`cohyp.V` SHOULD be pinned to. The switch-over is a separate, later step (`Spine.lean` is a
concurrent lane's write scope and `anchoredVInter` is deliberately left untouched). -/
noncomputable def anchoredVFullOn (Lat : PeriodicLatticeExtent) (Lambda : Finset (Bond Lat))
    (ell : ℕ) : Submodule ℝ (AnchoredBondSpace Lat) :=
  Submodule.map (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).symm.toLinearMap
    (admissibleSubspaceFullOn Lat Lambda ell)

/-- The full-torus specialization. -/
noncomputable def anchoredVFull (Lat : PeriodicLatticeExtent) (ell : ℕ) :
    Submodule ℝ (AnchoredBondSpace Lat) :=
  anchoredVFullOn Lat Finset.univ ell

/-- **RELATIONSHIP 1 — `anchoredVFull ≤ anchoredVInter`.** The repaired subspace is contained in
the one-clause object the goal statement currently uses. -/
theorem anchoredVFull_le_anchoredVInter (Lat : PeriodicLatticeExtent) (ell : ℕ) :
    anchoredVFull Lat ell ≤ anchoredVInter (Lat := Lat) ell := by
  unfold anchoredVFull anchoredVFullOn anchoredVInter
  exact Submodule.map_mono (admissibleSubspaceFull_le_inter (L := Lat) ell)

/-- Restricting `Λ` only shrinks the subspace further. -/
theorem anchoredVFullOn_le_anchoredVFull (Lat : PeriodicLatticeExtent)
    (Lambda : Finset (Bond Lat)) (ell : ℕ) :
    anchoredVFullOn Lat Lambda ell ≤ anchoredVFull Lat ell := by
  unfold anchoredVFull anchoredVFullOn admissibleSubspaceFullOn
  refine Submodule.map_mono (inf_le_inf_right _ (inf_le_inf_right _ ?_))
  intro B _hB b hb
  exact absurd (Finset.mem_univ b) hb

/-- Membership in the transported object, in terms of the bare-`Pi` representative. -/
theorem mem_anchoredVFull {Lat : PeriodicLatticeExtent} {ell : ℕ}
    {B : AnchoredBondSpace Lat} :
    B ∈ anchoredVFull Lat ell ↔
      (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)) B ∈ admissibleSubspaceFull Lat ell := by
  unfold anchoredVFull anchoredVFullOn admissibleSubspaceFull
  exact Submodule.mem_map_equiv (e := (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).symm) _

#print axioms anchoredVFullOn
#print axioms anchoredVFull_le_anchoredVInter
#print axioms anchoredVFullOn_le_anchoredVFull
#print axioms mem_anchoredVFull

/-! ## §5 — RELATIONSHIP 2: `anchoredVFull ≠ ⊥`, with an EXPLICIT witness

The witness is supported on direction-`2` bonds only, and is a `2`-shift-gradient in the `2`
coordinate multiplied by a factor that VANISHES on the coarse-aligned `0`-coordinate slices:

* the axial clause holds because every direction-`2` bond of a staircase `Γ_{y,x}` has base site
  agreeing with `y` in coordinate `0`, and `y ∈ Λ'` forces `(y 0).val % ell = 0`, where the factor
  is `0`;
* the `Q₁` clause holds POINTWISE in `x` — each individual length-`ell` line integral telescopes to
  `wLam(x + ell·e₂) − wLam(x) = 0` by periodicity — so no block-sum bookkeeping is needed at all.
-/

/-- Period-`ell` indicator on `ℕ`. -/
def wLamVal (ell t : ℕ) : ℝ := if t % ell = 0 then 1 else 0

/-- The site function whose `2`-gradient carries the witness. -/
def wLam (ell : ℕ) (z : PeriodicLatticeSite L) : ℝ := wLamVal ell (z 2).val

/-- **THE WITNESS.** Supported on direction-`2` bonds whose base has `(z 0).val % ell ≠ 0`. -/
noncomputable def wConfig (ell : ℕ) (b : Bond L) : ℝ :=
  if b.2 = 2 then (if (b.1 0).val % ell = 0 then 0 else gradValue (wLam ell) b) else 0

/-- `wLamVal` only sees its argument mod `ell`, so a `% N` with `ell ∣ N` is invisible to it. -/
theorem wLamVal_mod {ell N : ℕ} (hdvd : ell ∣ N) (t : ℕ) :
    wLamVal ell (t % N) = wLamVal ell t := by
  unfold wLamVal
  rw [Nat.mod_mod_of_dvd _ hdvd]

/-- **THE TELESCOPING IDENTITY (`ell ∣ L 2 + 1` load-bearing).** Every length-`ell` line integral
of the witness vanishes, at EVERY base site — before any block averaging. -/
theorem lineIntegralValue_wConfig_two {ell : ℕ} (hdvd : ell ∣ (L 2 + 1))
    (x : PeriodicLatticeSite L) :
    lineIntegralValue ell (wConfig (L := L) ell) x 2 = 0 := by
  rw [lineIntegralValue_eq_coarseShift]
  by_cases hx0 : (x 0).val % ell = 0
  · refine Finset.sum_eq_zero fun j _ => ?_
    have hcoord : (coarseShift x j 2) 0 = x 0 := coarseShift_apply_ne x j 2 0 (by decide)
    simp only [wConfig, hcoord, hx0, if_true]
  · have hterm : ∀ j : ℕ,
        wConfig (L := L) ell (coarseShift x j 2, 2) =
          wLam ell (coarseShift x (j + 1) 2) - wLam ell (coarseShift x j 2) := by
      intro j
      have hcoord : (coarseShift x j 2) 0 = x 0 := coarseShift_apply_ne x j 2 0 (by decide)
      have hsucc : periodicLatticeShift (coarseShift x j 2) 2 = coarseShift x (j + 1) 2 := by
        unfold coarseShift
        exact (Function.iterate_succ_apply' (fun z => periodicLatticeShift z 2) j x).symm
      simp only [wConfig, hcoord, if_neg hx0, if_true, gradValue, hsucc]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    rw [Finset.sum_range_sub (fun j => wLam (L := L) ell (coarseShift x j 2)) ell]
    have h0 : coarseShift x 0 2 = x := rfl
    have hell : wLam (L := L) ell (coarseShift x ell 2) = wLam ell x := by
      unfold wLam
      rw [coarseShift_val_eq x ell 2, wLamVal_mod hdvd]
      unfold wLamVal
      rw [Nat.add_mod_right]
    rw [h0, hell, sub_self]

/-- The witness lies in the axial-gauge clause — for EVERY `ell`, no hypothesis. -/
theorem wConfig_mem_admissibleSubspaceInter (ell : ℕ) :
    wConfig (L := L) ell ∈ admissibleSubspaceInter L ell := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x _hx b hb
  by_cases hd : b.2 = 2
  · -- `b` must be the direction-`2` segment, whose base site agrees with `y` in coordinate `0`
    have hseg : b ∈ axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val) := by
      unfold staircasePath at hb
      rcases Finset.mem_union.mp hb with hb' | hb'
      · rcases Finset.mem_union.mp hb' with hb'' | hb''
        · exact hb''
        · exact absurd ((mem_axisSegment.mp hb'').1) (by rw [hd]; decide)
      · exact absurd ((mem_axisSegment.mp hb').1) (by rw [hd]; decide)
    have hbase : b.1 0 = y 0 := (mem_axisSegment.mp hseg).2.1 0 (by decide)
    have hy0 : (y 0).val % ell = 0 := (mem_CoarseLattice.mp hy) 0
    simp only [wConfig, hd, hbase, hy0, if_true]
  · simp only [wConfig, if_neg hd]

/-- The witness lies in `ker Q₁`. -/
theorem wConfig_mem_kerQOne {ell : ℕ} (hdvd : ell ∣ (L 2 + 1)) :
    wConfig (L := L) ell ∈ kerQOne L ell := by
  rw [mem_kerQOne]
  intro c
  unfold lineCoarseRestrict
  by_cases hd : c.2 = 2
  · rw [Finset.sum_eq_zero fun x _ => by rw [hd]; exact lineIntegralValue_wConfig_two hdvd x]
    ring
  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ => ?_)
    rw [lineIntegralValue_eq_coarseShift]
    exact Finset.sum_eq_zero fun j _ => by simp only [wConfig, if_neg hd]

/-- The distinguished site `(1, 0, 0)`, where the witness is nonzero. -/
def wSite (h1 : 1 < L 0 + 1) : PeriodicLatticeSite L :=
  Function.update (fun μ => (0 : Fin (L μ + 1))) (0 : Fin 3) ⟨1, h1⟩

theorem wSite_zero (h1 : 1 < L 0 + 1) : ((wSite (L := L) h1) 0).val = 1 := by
  unfold wSite
  rw [Function.update_self]

theorem wSite_two (h1 : 1 < L 0 + 1) : ((wSite (L := L) h1) 2).val = 0 := by
  unfold wSite
  rw [Function.update_of_ne (by decide)]
  simp

/-- The witness's value at a direction-`2` bond, with the outer `if` discharged. -/
theorem wConfig_apply_two (ell : ℕ) (z : PeriodicLatticeSite L) :
    wConfig ell (z, (2 : Fin 3)) =
      if (z 0).val % ell = 0 then 0 else gradValue (wLam ell) (z, (2 : Fin 3)) := by
  unfold wConfig
  simp

/-- The `2`-gradient of `wLam`, unfolded. -/
theorem gradValue_wLam (ell : ℕ) (z : PeriodicLatticeSite L) :
    gradValue (wLam ell) (z, (2 : Fin 3)) =
      wLamVal ell ((periodicLatticeShift z 2) 2).val - wLamVal ell (z 2).val := rfl

/-- **The witness is nonzero** (needs `2 ≤ ell`, and `ell ∣ L μ + 1` only to know the lattice is
big enough in directions `0` and `2`). Its value at the bond `⟨(1,0,0), e₂⟩` is `-1`. -/
theorem wConfig_ne_zero {ell : ℕ} (hell : 2 ≤ ell) (hdvd0 : ell ∣ (L 0 + 1))
    (hdvd2 : ell ∣ (L 2 + 1)) : wConfig (L := L) ell ≠ 0 := by
  have h0 : 2 ≤ L 0 + 1 := le_trans hell (Nat.le_of_dvd (Nat.succ_pos _) hdvd0)
  have h2 : 2 ≤ L 2 + 1 := le_trans hell (Nat.le_of_dvd (Nat.succ_pos _) hdvd2)
  have h1 : 1 < L 0 + 1 := by omega
  have hshift : ((periodicLatticeShift (wSite (L := L) h1) 2) 2).val = 1 := by
    rw [periodicLatticeShift_self, Fin.val_add, wSite_two h1, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : 1 < L 2 + 1), Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < L 2 + 1)]
  have hval : wConfig (L := L) ell (wSite h1, (2 : Fin 3)) = -1 := by
    rw [wConfig_apply_two, wSite_zero h1, Nat.mod_eq_of_lt (by omega : 1 < ell),
      if_neg (by omega : ¬ (1 : ℕ) = 0), gradValue_wLam, hshift, wSite_two h1]
    unfold wLamVal
    rw [Nat.mod_eq_of_lt (by omega : 1 < ell), if_neg (by omega : ¬ (1 : ℕ) = 0),
      Nat.zero_mod, if_pos rfl]
    norm_num
  intro hzero
  rw [hzero] at hval
  norm_num at hval

/-- **RELATIONSHIP 2 — `admissibleSubspaceFull ≠ ⊥` for `2 ≤ ell` under tileability.** -/
theorem admissibleSubspaceFull_ne_bot {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) : admissibleSubspaceFull L ell ≠ ⊥ := by
  intro hbot
  have hmem : wConfig (L := L) ell ∈ admissibleSubspaceFull L ell := by
    rw [mem_admissibleSubspaceFull]
    refine ⟨?_, ?_⟩
    · rw [← mem_admissibleSubspaceInter]; exact wConfig_mem_admissibleSubspaceInter ell
    · rw [← mem_kerQOne]; exact wConfig_mem_kerQOne (hdvd 2)
  rw [hbot, Submodule.mem_bot] at hmem
  exact wConfig_ne_zero hell (hdvd 0) (hdvd 2) hmem

/-- **RELATIONSHIP 2, transported — `anchoredVFull ≠ ⊥`.** This is what
`CoercivityHypothesis.V_ne_bot` needs at the repaired domain. -/
theorem anchoredVFull_ne_bot {Lat : PeriodicLatticeExtent} {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (Lat μ + 1)) : anchoredVFull Lat ell ≠ ⊥ := by
  unfold anchoredVFull anchoredVFullOn
  rw [Submodule.map_ne_bot_iff]
  exact admissibleSubspaceFull_ne_bot hell hdvd

#print axioms wLamVal_mod
#print axioms lineIntegralValue_wConfig_two
#print axioms wConfig_mem_admissibleSubspaceInter
#print axioms wConfig_mem_kerQOne
#print axioms wConfig_apply_two
#print axioms gradValue_wLam
#print axioms wConfig_ne_zero
#print axioms admissibleSubspaceFull_ne_bot
#print axioms anchoredVFull_ne_bot

/-! ## §6 — RELATIONSHIP 3: the inclusion is STRICT

A single-bond configuration on the bond whose base sits at coordinate-`0` offset `ell − 1` — the
one direction-`0` bond of each block that NO staircase reaches — satisfies the axial clause and
violates `Q₁B = 0`. (This is Bałaban's own `b₀`: p.428's "`B(c) ∩ c` consists of the exactly one
bond `b₀` of `B(c)` contained in `c`", the variable his `C` eliminates using `(QB)(c) = 0`. So the
strictness witness is not an artifact — it is the very variable the `Q₁` clause is there to fix.) -/

/-- The site `(ell − 1, 0, 0)`. -/
def strictSite {ell : ℕ} (h : ell - 1 < L 0 + 1) : PeriodicLatticeSite L :=
  Function.update (fun μ => (0 : Fin (L μ + 1))) (0 : Fin 3) ⟨ell - 1, h⟩

theorem strictSite_zero {ell : ℕ} (h : ell - 1 < L 0 + 1) :
    ((strictSite (L := L) (ell := ell) h) 0).val = ell - 1 := by
  unfold strictSite
  rw [Function.update_self]

theorem strictSite_ne {ell : ℕ} (h : ell - 1 < L 0 + 1) {ν : Fin 3} (hν : ν ≠ 0) :
    ((strictSite (L := L) (ell := ell) h) ν).val = 0 := by
  unfold strictSite
  rw [Function.update_of_ne hν]
  simp

/-- The bond `⟨(ell−1,0,0), direction 0⟩`. -/
def strictBond {ell : ℕ} (h : ell - 1 < L 0 + 1) : Bond L :=
  (strictSite (L := L) (ell := ell) h, (0 : Fin 3))

/-- The single-bond configuration at `strictBond`. -/
noncomputable def strictConfig {ell : ℕ} (h : ell - 1 < L 0 + 1) : Bond L → ℝ :=
  fun b => if b = strictBond (L := L) (ell := ell) h then 1 else 0

/-- `strictConfig` satisfies the AXIAL clause: no staircase contains `strictBond`. -/
theorem strictConfig_mem_admissibleSubspaceInter {ell : ℕ} (hell : 2 ≤ ell)
    (h : ell - 1 < L 0 + 1) :
    strictConfig (L := L) (ell := ell) h ∈ admissibleSubspaceInter L ell := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x hx b hb
  unfold strictConfig
  rw [if_neg]
  intro hbe
  have hd : b.2 = 0 := by rw [hbe]; rfl
  -- so `b` lies in the direction-`0` segment
  have hseg : b ∈ axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val)
      (max (y 0).val (x 0).val) := by
    unfold staircasePath at hb
    rcases Finset.mem_union.mp hb with hb' | hb'
    · rcases Finset.mem_union.mp hb' with hb'' | hb''
      · exact absurd ((mem_axisSegment.mp hb'').1) (by rw [hd]; decide)
      · exact absurd ((mem_axisSegment.mp hb'').1) (by rw [hd]; decide)
    · exact hb'
  obtain ⟨-, -, hlo, hhi⟩ := mem_axisSegment.mp hseg
  have hblk := (mem_blockOf.mp hx) 0
  have hmin : min (y 0).val (x 0).val = (y 0).val := by omega
  have hmax : max (y 0).val (x 0).val = (x 0).val := by omega
  rw [hmin] at hlo
  rw [hmax] at hhi
  have hb0 : (b.1 0).val = ell - 1 := by
    rw [hbe]
    exact strictSite_zero h
  have hy0 : (y 0).val % ell = 0 := (mem_CoarseLattice.mp hy) 0
  have hyzero : (y 0).val = 0 :=
    Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hy0) (by omega)
  omega

/-- `strictConfig` VIOLATES `Q₁B = 0` — the coarse bond at the origin in direction `0` sees it. -/
theorem strictConfig_not_mem_kerQOne {ell : ℕ} (hell : 2 ≤ ell) (h : ell - 1 < L 0 + 1) :
    strictConfig (L := L) (ell := ell) h ∉ kerQOne L ell := by
  intro hker
  rw [mem_kerQOne] at hker
  have horigin : (fun μ => (0 : Fin (L μ + 1))) ∈ CoarseLattice L ell := by
    rw [mem_CoarseLattice]; intro μ; simp
  have hval := hker (⟨_, horigin⟩, (0 : Fin 3))
  unfold lineCoarseRestrict at hval
  -- every summand is nonnegative, and the summand at `strictSite` is at least `1`
  have hnonneg : ∀ x ∈ blockOf (fun μ => (0 : Fin (L μ + 1))) ell,
      (0 : ℝ) ≤ lineIntegralValue ell (strictConfig (L := L) (ell := ell) h) x 0 := by
    intro x _
    rw [lineIntegralValue_eq_coarseShift]
    refine Finset.sum_nonneg fun j _ => ?_
    unfold strictConfig
    split <;> norm_num
  have hsite : (strictSite (L := L) (ell := ell) h) ∈
      blockOf (fun μ => (0 : Fin (L μ + 1))) ell := by
    rw [mem_blockOf]
    intro μ
    by_cases hμ : μ = 0
    · subst hμ; rw [strictSite_zero h]; simp; omega
    · rw [strictSite_ne h hμ]; simp; omega
  have hpos : (0 : ℝ) < lineIntegralValue ell (strictConfig (L := L) (ell := ell) h)
      (strictSite (L := L) (ell := ell) h) 0 := by
    rw [lineIntegralValue_eq_coarseShift]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    · unfold strictConfig; split <;> norm_num
    · unfold strictConfig
      rw [if_pos (by rw [show coarseShift (strictSite (L := L) (ell := ell) h) 0 0
            = strictSite (L := L) (ell := ell) h from rfl]; rfl)]
      norm_num
  have hsum : (0 : ℝ) < ∑ x ∈ blockOf (fun μ => (0 : Fin (L μ + 1))) ell,
      lineIntegralValue ell (strictConfig (L := L) (ell := ell) h) x 0 :=
    Finset.sum_pos' hnonneg ⟨_, hsite, hpos⟩
  have hcoef : (0 : ℝ) < 1 / (ell : ℝ) ^ 4 := by
    have hellR : (0 : ℝ) < (ell : ℝ) := by
      have : 0 < ell := by omega
      exact_mod_cast this
    positivity
  nlinarith [hval, hsum, hcoef]

/-- **STRICTNESS at the bare carrier** — the exhibited field lies in `admissibleSubspaceInter` and
NOT in `admissibleSubspaceFull`. -/
theorem admissibleSubspaceFull_lt_inter {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd0 : ell ∣ (L 0 + 1)) :
    admissibleSubspaceFull L ell < admissibleSubspaceInter L ell := by
  have hle : ell ≤ L 0 + 1 := Nat.le_of_dvd (Nat.succ_pos _) hdvd0
  have h : ell - 1 < L 0 + 1 := by omega
  refine lt_of_le_of_ne (admissibleSubspaceFull_le_inter ell) ?_
  intro heq
  have hin : strictConfig (L := L) (ell := ell) h ∈ admissibleSubspaceInter L ell :=
    strictConfig_mem_admissibleSubspaceInter hell h
  rw [← heq, mem_admissibleSubspaceFull] at hin
  exact strictConfig_not_mem_kerQOne hell h (mem_kerQOne.mpr hin.2)

/-- **RELATIONSHIP 3 — the inclusion is STRICT**, transported. `Submodule.map` along a linear
EQUIVALENCE is a strict-order embedding (`Submodule.map_lt_map_iff_of_injective`), so the strictness
carries exactly. -/
theorem anchoredVFull_lt_anchoredVInter {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd0 : ell ∣ (L 0 + 1)) :
    anchoredVFull L ell < anchoredVInter (Lat := L) ell := by
  unfold anchoredVFull anchoredVFullOn anchoredVInter
  rw [Submodule.map_lt_map_iff_of_injective
    (WithLp.linearEquiv 2 ℝ (Bond L → ℝ)).symm.injective]
  exact admissibleSubspaceFull_lt_inter hell hdvd0

/-- **CONTROL — the `Q₁` clause is NOT `⊤` for `2 ≤ ell`.** Without this, `kerQOne` could in
principle be the whole space and `anchoredVFull` would silently equal `anchoredVInter`; the added
clause would then be decoration. The exhibited `strictConfig` refutes that at every tileable
lattice. -/
theorem kerQOne_ne_top {ell : ℕ} (hell : 2 ≤ ell) (hdvd0 : ell ∣ (L 0 + 1)) :
    kerQOne L ell ≠ ⊤ := by
  have hle : ell ≤ L 0 + 1 := Nat.le_of_dvd (Nat.succ_pos _) hdvd0
  have h : ell - 1 < L 0 + 1 := by omega
  intro htop
  exact strictConfig_not_mem_kerQOne hell h (by rw [htop]; exact Submodule.mem_top)

#print axioms strictConfig_mem_admissibleSubspaceInter
#print axioms strictConfig_not_mem_kerQOne
#print axioms kerQOne_ne_top
#print axioms admissibleSubspaceFull_lt_inter
#print axioms anchoredVFull_lt_anchoredVInter

/-! ## §7 — THE `ell ∈ {0,1}` DEGENERATION, and the `ell = 1` OBSTRUCTION -/

/-- `anchoredVInter 1 = ⊤` at the bare carrier: `B(y) = {y}` and `Γ_{y,y} = ∅`. -/
theorem admissibleSubspaceInter_one_eq_top : admissibleSubspaceInter L 1 = ⊤ := by
  ext B
  rw [mem_admissibleSubspaceInter]
  simp only [Submodule.mem_top, iff_true]
  intro y _ x hx b hb
  rw [blockOf_one_eq_singleton, Finset.mem_singleton] at hx
  subst hx
  rw [staircasePath_self] at hb
  exact absurd hb (Finset.notMem_empty b)

/-- `anchoredVInter 0 = ⊤` at the bare carrier: `B(y) = ∅`. -/
theorem admissibleSubspaceInter_zero_eq_top : admissibleSubspaceInter L 0 = ⊤ := by
  ext B
  rw [mem_admissibleSubspaceInter]
  simp only [Submodule.mem_top, iff_true]
  intro y _ x hx
  rw [blockOf_zero_empty] at hx
  exact absurd hx (Finset.notMem_empty x)

/-- **`Q₁` at `ell = 1` is the IDENTITY read-off**: `(Q₁B)(y,μ) = B(y,μ)`. -/
theorem lineCoarseRestrict_one_apply (B : Bond L → ℝ) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L 1) (μ : Fin 3) :
    lineCoarseRestrict 1 B ((⟨y, hy⟩ : {z // z ∈ CoarseLattice L 1}), μ) = B (y, μ) := by
  unfold lineCoarseRestrict
  rw [show ((⟨y, hy⟩ : {z // z ∈ CoarseLattice L 1}), μ).1.1 = y from rfl,
    show ((⟨y, hy⟩ : {z // z ∈ CoarseLattice L 1}), μ).2 = μ from rfl]
  rw [blockOf_one_eq_singleton, Finset.sum_singleton]
  unfold lineIntegralValue
  rw [Finset.sum_range_one]
  simp

/-- **`ker Q₁ = ⊥` at `ell = 1`.** The ℝ-carrier, FLAT analogue of
`CoercivitySupply.memKerQ_one_implies_zero` (su(2) carrier, covariant `Q`); an independent proof on
a different carrier, converging on the same collapse. -/
theorem kerQOne_one_eq_bot : kerQOne L 1 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro B hB
  rw [mem_kerQOne] at hB
  funext b
  have := hB (⟨b.1, mem_coarseLattice_one b.1⟩, b.2)
  rw [lineCoarseRestrict_one_apply] at this
  exact this

/-- `ker Q₁ = ⊤` at `ell = 0` (both `1/0⁴` and the empty block make it identically zero). -/
theorem kerQOne_zero_eq_top : kerQOne L 0 = ⊤ := by
  rw [eq_top_iff]
  intro B _
  rw [mem_kerQOne]
  intro c
  unfold lineCoarseRestrict
  rw [blockOf_zero_empty, Finset.sum_empty, mul_zero]

/-- **THE `ell = 1` OBSTRUCTION, LOUD: `anchoredVFull 1 = ⊥`.** The faithful three-condition
subspace is the ZERO subspace at `ell = 1`. Any coercivity statement over it is vacuous, and
`CoercivityHypothesis.V_ne_bot` is UNSATISFIABLE there — see
`no_coercivityHypothesis_at_anchoredVFull_one`. Contrast `anchoredVInter 1 = ⊤`
(`Anchoring.anchoredVInter` + `admissibleSubspaceInter_one_eq_top`): the one-clause object
degenerates UPWARD to everything, the faithful object degenerates DOWNWARD to nothing. Neither is
the intended statement, and they fail in opposite directions. -/
theorem anchoredVFull_one_eq_bot (Lat : PeriodicLatticeExtent) : anchoredVFull Lat 1 = ⊥ := by
  unfold anchoredVFull anchoredVFullOn admissibleSubspaceFullOn
  rw [kerQOne_one_eq_bot, inf_bot_eq, Submodule.map_bot]

/-- `anchoredVFull 0 = ⊤` — total degeneration, all three clauses vacuous. -/
theorem anchoredVFull_zero_eq_top (Lat : PeriodicLatticeExtent) : anchoredVFull Lat 0 = ⊤ := by
  unfold anchoredVFull anchoredVFullOn admissibleSubspaceFullOn
  rw [kerQOne_zero_eq_top, admissibleSubspaceInter_zero_eq_top, lambdaSupported_univ,
    top_inf_eq, top_inf_eq]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (WithLp.linearEquiv 2 ℝ (Bond Lat → ℝ)).symm.surjective

/-- **The `ell = 1` obstruction, as a statement about the goal's own structure.** No
`CoercivityHypothesis` term can have `V = anchoredVFull Lat 1`, because `V_ne_bot` is a mandatory
field. So the goal is NOT STATABLE at `ell = 1` over the faithful domain — this must be a
hypothesis (`2 ≤ ell`) on every consumer, not an omission. -/
theorem no_coercivityHypothesis_at_anchoredVFull_one (Lat : PeriodicLatticeExtent)
    {Uconfig : Type} [Nontrivial Uconfig]
    (cohyp : CoercivityHypothesis (AnchoredBondSpace Lat) Uconfig)
    (hV : cohyp.V = anchoredVFull Lat 1) : False :=
  cohyp.V_ne_bot (by rw [hV, anchoredVFull_one_eq_bot])

#print axioms admissibleSubspaceInter_one_eq_top
#print axioms admissibleSubspaceInter_zero_eq_top
#print axioms lineCoarseRestrict_one_apply
#print axioms kerQOne_one_eq_bot
#print axioms kerQOne_zero_eq_top
#print axioms anchoredVFull_one_eq_bot
#print axioms anchoredVFull_zero_eq_top
#print axioms no_coercivityHypothesis_at_anchoredVFull_one

/-! ## §8 — MADE-IT-FAIL CONTROLS, and the named residuals

The controls below are the "try to inhabit your own definitions degenerately" requirement: each is a
FAILED attempt kept as a theorem, so a later reader cannot mistake the §5 hypotheses for decoration.
-/

/-- **CONTROL 1 — the §5 witness COLLAPSES at `ell = 1`.** `(z 0).val % 1 = 0` always, so `wConfig`
is identically zero exactly at the degenerate scale. The witness therefore does NOT accidentally
survive at the test point where distinct alternatives coincide. -/
theorem wConfig_one_eq_zero : wConfig (L := L) 1 = 0 := by
  funext b
  show wConfig 1 b = 0
  simp [wConfig, Nat.mod_one]

/-- **CONTROL 2 — the divisibility hypothesis is LOAD-BEARING.** The window-sum mechanism behind
`lineIntegralValue_wConfig_two` fails at `(ell, N) = (2, 3)`: summing `wLamVal 2` over the `2`
consecutive residues starting at `1` mod `3` gives `1`, not `0`. Proved by direct evaluation, so it
is a computed failure, not an argument that it would fail. -/
theorem window_sum_fails_without_dvd :
    (∑ j ∈ Finset.range 2, wLamVal 2 ((1 + j) % 3)) = 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wLamVal]

#print axioms wConfig_one_eq_zero
#print axioms window_sum_fails_without_dvd

/-! ### NAMED RESIDUALS (earned, not elected — OPS-1)

* **`[LAMBDA-BOND-SET]`** — `lambdaSupported` takes the bond set of `Λ` as a PARAMETER, because the
  source uses the symbol `Λ` for BOTH a site region and its bond set and never states the reduction.
  ATTEMPTED, with the exact point of failure:
  - p.427 §E introduces `Λ` as SITES ("some domain `Λ` of the unit lattice … `Λ` is a union of big
    blocks");
  - p.427 then says `g` is "defined at bonds of `Λ`", and p.428 says `B` is restricted "to the set
    of bonds `Λ̃ = Λ \ (⋃Ax(y) ∪ ⋃B(c)∩c)`" — so on p.428 `Λ` DENOTES A BOND SET, by abuse;
  - a full-text search of CMP99b and CMP96 for the phrases that would pin it (`bonds of`,
    `bonds in`, `bonds contained`, `Dirichlet`) returns only "Dirichlet boundary conditions
    outside/on `Λᶜ`" and "defined at bonds of `Λ`" — never a bond-set definition. `dB↾_Λ` restricts
    the MEASURE, not the index set.
  So "base in `Λ`", "both endpoints in `Λ`" and "touches `Λ`" all read consistently with the prose
  and are DIFFERENT sets — the S83 quantifier-weakening class, already exhibited as a proved-distinct
  pair in this tree at `Blocks.bondsTouching` / `Blocks.bondsBothEndpointsIn` (with
  `Blocks.bondsBothEndpointsIn_subset_bondsTouching` and the standing regression guard
  `Probes.bondsTouching_ne_bondsBothEndpointsIn_witness`). NOT rebuilt here (LAW-19); those live on
  the `Finset (Site × Site)` carrier, this module's is `Bond L = Site × Fin 3`.
  RESISTANCE: closing it needs an adjudication of CMP96 §2 (pp.243-249) at page-image level, a
  separate source pass, not a Lean step. `DomainSequence.LambdaKDomain.Lambda` already supplies `Λ`
  as a SITE `Finset` with `IsValid` (`Λ ⊂ Λ_k`, `RM` margin) — that is the object to connect to once
  the convention is pinned, and its being site-valued is independent confirmation that the tree does
  not yet hold the bond convention either. The parameter keeps the object honest meanwhile, and the
  full-torus case the tree actually uses is unaffected (`lambdaSupported_univ`).
* **`[Q1-BACKGROUND-ARG]`** — inherited unchanged from `compute/q1_adjudication/RULING.md` §3: which
  configuration `V` enters `Q(V)`'s conjugation for the unit-lattice-to-`Λ'` step. Irrelevant at
  THIS carrier (no `Ad` action on a one-dimensional real fibre), decisive on the su(2) carrier.
* **`[COERCHYP-V-NOT-U-INDEXED]`** — NEW, created by this pass and disclosed here rather than
  spawned silently. `CoercivityHypothesis.V : Submodule ℝ H` is `U`-INDEPENDENT by type. The
  faithful `Q₁` clause is `U`-dependent (module docstring), so on the su(2) carrier the admissible
  subspace MOVES with the background and cannot inhabit that field at all. ATTEMPTED in-pass: the
  only `U`-free repair available at the ℝ-carrier is the flat clause, which is what this module
  builds — so the residual is not closable here without changing `CoercivityHypothesis`'s field
  type, and `Balaban/Coercivity.lean` is a concurrent lane's write scope (LAW-4). REPORTED.
* **NOT a residual, stated to prevent a fourth construction (GOAL_LEMMA §6.7):** the su(2)
  `U`-dependent two-clause domain ALREADY EXISTS as `CoercivitySupply.Admissible`. This module is
  the ℝ-carrier `Submodule` counterpart the SPINE's own carrier demands, not a rival object.
-/

end AdalyFormal.Balaban.AnchoredVFull
