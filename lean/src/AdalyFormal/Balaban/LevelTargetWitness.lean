import AdalyFormal.Balaban.ThirdLevelSchurGap

set_option autoImplicit false

/-!
# `LevelTargetWitness` — a `Btil` satisfying BOTH clauses of the level-corrected target

## Why this file exists

`ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` quantifies over `Btil` under **two**
hypotheses (`ThirdLevelSchurGap.lean`, the two lines above the conclusion):

* the **axial-gauge** clause — `∀ y' ∈ CoarseLattice L S.constr, ∀ x ∈ blockOf y' S.constr,
  ∀ e ∈ staircasePath y' x, Btil e = 0`;
* the **dropped-bond** clause — `∀ c : CoarseBond L S.constr, Btil (droppedBondLast S.constr c) = 0`.

A prosecution (2026-07-29, `compute/levelcorrected_attack/`) found that the tree's only offered
non-vacuity witness, `ThirdLevelWitness.B7`, satisfies the **second** clause and **fails the first**
(`B7_fails_axial_gauge`, compiled and axiom-clean). It also measured that `staircasePath` occurs
exactly **once** in the whole cluster — inside the target's own definition — and **zero** times in
`ThirdLevelSandwich`, `ThirdLevelWitness` or `CStarLevelCorrected`: the axial clause had never been
checked against any witness at all.

So before this file the tree contained **no** evidence that the target is satisfiable. This file
supplies that evidence.

## The mechanism, and it is short

Unfolding `staircasePath y x = axisSegment y 2 … ∪ axisSegment (corner1 y x) 1 … ∪
axisSegment (corner2 y x) 0 …`, every bond in a staircase satisfies `e.2 ∈ ({0,1,2} : Set (Fin 3))`
with the **transverse coordinates pinned to the segment's base**. In particular a bond of direction
`2` can only lie in the *first* segment, whose base is `y` itself — so it must satisfy
`e.1 0 = y 0`.

But `y ∈ CoarseLattice L ell` forces `(y 0).val % ell = 0`, and for `2 ≤ ell` the value `1` is not
`≡ 0 mod ell`. **Hence no direction-`2` bond whose base has coordinate `0` equal to `1` lies on any
staircase**, for any coarse `y` and any `x` whatsoever — no block-membership reasoning needed.

The same one line kills the dropped-bond clause: `droppedBondLast ell c = (pathSite c.1.1 c.2 (ell-1),
c.2)`, and `pathSite` shifts only along `c.2`, so at `c.2 = 2` the base's coordinate `0` equals
`(c.1.1) 0` — again a coarse site's, hence `≠ 1`.

`oneSite` is the site with coordinate `0` equal to `1` and the others `0`; `wBond` is `(oneSite, 2)`;
`wField` is `Pi.single wBond suTwoWitness`. The target's own hypothesis `∀ μ, 4 ≤ L μ` supplies
`1 < L 0 + 1`, so `oneSite` exists.

## Scope — what this file does NOT claim

It establishes **satisfiability of the two clauses with positive `bondEnergy`**, which is exactly the
evidence the prosecution found missing. It does **not** evaluate `cStarDeltaKCFormCorr` at `wField`,
and so says nothing about whether the target's *inequality* holds or fails here — the separate and
harder question. Nothing here is a coercivity bound.
-/

namespace AdalyFormal.Balaban.LevelTargetWitness

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.LatticeOperators

variable {L : PeriodicLatticeExtent}

/-! ### §1 — the arithmetic fact the whole file rests on -/

/-- **A coarse site never has a coordinate equal to `1`, once `2 ≤ ell`.** `1 % ell = 1 ≠ 0`. -/
theorem coarse_coord_ne_one {ell : ℕ} (hell : 2 ≤ ell)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    (y μ).val ≠ 1 := by
  intro h
  have h0 : (y μ).val % ell = 0 := (mem_CoarseLattice).1 hy μ
  rw [h, Nat.one_mod_eq_zero_iff] at h0
  omega

/-! ### §2 — the witness site and bond -/

/-- The site with coordinate `0` equal to `1` and the other two coordinates `0`. Well-defined
because the target's own hypothesis gives `4 ≤ L μ`, hence `1 < L μ + 1`. -/
def oneSite (h : ∀ μ : Fin 3, 4 ≤ L μ) : PeriodicLatticeSite L :=
  fun μ => if μ = 0 then ⟨1, by have := h μ; omega⟩ else ⟨0, by have := h μ; omega⟩

theorem oneSite_zero (h : ∀ μ : Fin 3, 4 ≤ L μ) : ((oneSite h) 0).val = 1 := by
  simp [oneSite]

/-- The witness bond: direction `2`, based at `oneSite`. -/
def wBond (h : ∀ μ : Fin 3, 4 ≤ L μ) : PeriodicLatticeEdge L := (oneSite h, 2)

theorem wBond_dir (h : ∀ μ : Fin 3, 4 ≤ L μ) : (wBond h).2 = 2 := rfl

theorem wBond_base_zero (h : ∀ μ : Fin 3, 4 ≤ L μ) : ((wBond h).1 0).val = 1 :=
  oneSite_zero h

/-! ### §3 — the witness bond is on NO staircase -/

/-- **The axial clause, at the level of the single bond.** For every coarse `y`, every `x`, and every
`ell ≥ 2`, `wBond ∉ staircasePath y x`. The direction forces the first segment, whose base is `y`;
that pins coordinate `0` to `y 0`, which cannot be `1`. -/
theorem wBond_not_mem_staircasePath {ell : ℕ} (hell : 2 ≤ ell)
    (h : ∀ μ : Fin 3, 4 ≤ L μ)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) :
    wBond h ∉ staircasePath y x := by
  intro hmem
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hmem
  rcases hmem with (h2 | h1) | h0
  · -- direction-2 segment, base `y`: coordinate `0` is pinned to `y 0`
    rw [mem_axisSegment] at h2
    have hbase := h2.2.1 0 (by decide)
    have : ((wBond h).1 0).val = (y 0).val := by rw [hbase]
    rw [wBond_base_zero h] at this
    exact coarse_coord_ne_one hell hy 0 this.symm
  · -- direction-1 segment: the bond's direction is `2`, contradiction
    rw [mem_axisSegment] at h1
    have : (2 : Fin 3) = 1 := by rw [← wBond_dir h, h1.1]
    exact absurd this (by decide)
  · -- direction-0 segment: same
    rw [mem_axisSegment] at h0
    have : (2 : Fin 3) = 0 := by rw [← wBond_dir h, h0.1]
    exact absurd this (by decide)

/-! ### §4 — the witness bond is NOT a dropped bond -/

/-- `pathSite` moves only the coordinate it shifts, so at direction `2` the base's coordinate `0` is
unchanged. -/
theorem pathSite_coord_zero_of_dir_two (s : PeriodicLatticeSite L) (i : ℕ) :
    ((QOne.pathSite s 2 i) 0).val = (s 0).val := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [QOne.pathSite, Function.iterate_succ_apply'] at *
      show ((Function.update ((fun z => periodicLatticeShift z 2)^[n] s) 2 _) 0).val = _
      rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2)]
      exact ih

/-- **The dropped-bond clause, at the level of the single bond.** -/
theorem wBond_ne_droppedBondLast {ell : ℕ} (hell : 2 ≤ ell)
    (h : ∀ μ : Fin 3, 4 ≤ L μ) (c : CoarseBond L ell) :
    wBond h ≠ ReparamCDisjoint.droppedBondLast ell c := by
  intro heq
  by_cases hc2 : c.2 = (2 : Fin 3)
  · -- direction `2`: coordinate `0` of the base is the coarse site's, hence `≠ 1`
    have hbase : ((ReparamCDisjoint.droppedBondLast ell c).1 0).val = ((c.1.1) 0).val := by
      rw [ReparamCDisjoint.droppedBondLast, hc2]
      exact pathSite_coord_zero_of_dir_two _ _
    have hval : ((wBond h).1 0).val = ((c.1.1) 0).val := by rw [heq, hbase]
    rw [wBond_base_zero h] at hval
    exact coarse_coord_ne_one hell c.1.2 0 hval.symm
  · -- otherwise the two bonds already differ in their direction component
    apply hc2
    have : (wBond h).2 = (ReparamCDisjoint.droppedBondLast ell c).2 := by rw [heq]
    rw [wBond_dir h] at this
    exact this.symm

/-! ### §5 — the field, and BOTH clauses -/

/-- The witness field: `suTwoWitness` on `wBond`, zero elsewhere. -/
noncomputable def wField (h : ∀ μ : Fin 3, 4 ≤ L μ) : Bond L → SuTwo :=
  Pi.single (wBond h) suTwoWitness

theorem wField_apply_self (h : ∀ μ : Fin 3, 4 ≤ L μ) :
    wField h (wBond h) = suTwoWitness := by
  simp [wField]

theorem wField_apply_of_ne (h : ∀ μ : Fin 3, 4 ≤ L μ) {e : Bond L} (hne : e ≠ wBond h) :
    wField h e = 0 := by
  simp [wField, Pi.single_apply, hne]

/-- **CLAUSE 1 — the axial-gauge clause, in the target's own literal form.** -/
theorem wField_axial {ell : ℕ} (hell : 2 ≤ ell) (h : ∀ μ : Fin 3, 4 ≤ L μ) :
    ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, wField h e = 0 := by
  intro y' hy' x _hx e he
  exact wField_apply_of_ne h (fun hcon => wBond_not_mem_staircasePath hell h hy' x (hcon ▸ he))

/-- **CLAUSE 2 — the dropped-bond clause, in the target's own literal form.** -/
theorem wField_dropped {ell : ℕ} (hell : 2 ≤ ell) (h : ∀ μ : Fin 3, 4 ≤ L μ) :
    ∀ c : CoarseBond L ell, wField h (ReparamCDisjoint.droppedBondLast ell c) = 0 := by
  intro c
  exact wField_apply_of_ne h fun hcon => wBond_ne_droppedBondLast hell h c hcon.symm

/-! ### §6 — the energy is strictly positive -/

/-- **The witness is not the zero field**, so the target's conclusion is not trivially satisfied at
it: `bondEnergy` is bounded below by the single active bond's norm-square. -/
theorem wField_bondEnergy_pos (h : ∀ μ : Fin 3, 4 ≤ L μ) :
    0 < RegularUPerturbation.bondEnergy (wField h) := by
  have hne : wField h (wBond h) ≠ 0 := by
    rw [wField_apply_self h]; exact suTwoWitness_ne_zero
  have hpos : 0 < ‖wField h (wBond h)‖ ^ 2 := by positivity
  refine lt_of_lt_of_le hpos ?_
  refine Finset.single_le_sum (f := fun b : Bond L => ‖wField h b‖ ^ 2) ?_ (Finset.mem_univ _)
  intro b _
  positivity

/-! ### §7 — BOTH CLAUSES AND POSITIVE ENERGY, TOGETHER

This is the statement the prosecution found the tree unable to make. -/

/-- **THE TARGET'S DOMAIN IS NON-EMPTY.** At every lattice satisfying the target's own extent
hypothesis and every `ell ≥ 2`, there is a field satisfying **both** of the target's `Btil` clauses
with **strictly positive** `bondEnergy`.

Scope, restated so it is not mis-read: this is satisfiability of the two HYPOTHESES, which is what
was missing. It says nothing about whether the target's INEQUALITY holds at this field. -/
theorem target_domain_nonempty {ell : ℕ} (hell : 2 ≤ ell) (h : ∀ μ : Fin 3, 4 ≤ L μ) :
    ∃ Btil : Bond L → SuTwo,
      (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
        ∀ e ∈ staircasePath y' x, Btil e = 0) ∧
      (∀ c : CoarseBond L ell, Btil (ReparamCDisjoint.droppedBondLast ell c) = 0) ∧
      0 < RegularUPerturbation.bondEnergy Btil :=
  ⟨wField h, wField_axial hell h, wField_dropped hell h, wField_bondEnergy_pos h⟩

/-! ### §8 — controls

Must-fire and must-not-fire, so the theorem above is not passing for an empty reason. -/

/-- **MUST-NOT-FIRE.** The zero field satisfies both clauses too — and is excluded by the energy
conjunct. So the energy requirement is doing work. -/
theorem zero_field_satisfies_clauses_but_not_energy {ell : ℕ} :
    (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, (0 : Bond L → SuTwo) e = 0) ∧
    (∀ c : CoarseBond L ell,
      (0 : Bond L → SuTwo) (ReparamCDisjoint.droppedBondLast ell c) = 0) ∧
    ¬ (0 < RegularUPerturbation.bondEnergy (0 : Bond L → SuTwo)) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ => rfl, ?_⟩
  simp [RegularUPerturbation.bondEnergy]

/-! ### §9 — TWO REPAIRS FROM A BLIND SECOND-FAMILY GATE (2026-07-29)

A blind Sol gate read this module with its header stripped and no access to git or `GOAL_LEMMA.md`.
It **acquitted** the central claim — it re-derived both non-membership arguments from the raw
definitions rather than checking mine, and confirmed the two clauses are an exact unweakened match to
the target's antecedents after `ell := S.constr`. It also found two things, one a real defect of mine.

**DEFECT 1, and it was mine.** `zero_field_satisfies_clauses_but_not_energy` was named and documented
as showing the zero field satisfies "both clauses" — and its **type contained only the axial one**.
The dropped-bond conjunct was missing. True but unstated, which is precisely the docstring-versus-
declaration gap this campaign keeps convicting elsewhere. **Fixed above**: the conjunct is now in the
statement, so the control proves what its name says.

**CONCERN 2, which dissolves — and the reason it was raised is my briefing error.** The gate observed
that the target hypothesises `2 ≤ S.fibre` while both `Btil` clauses are stated at `S.constr`, and
warned that if `LevelSplit` permitted `S.constr = 1` then `droppedBondLast 1` would be the identity on
bonds, forcing `Btil = 0` and making this witness inapplicable. It could not settle this because
**I did not give it `CStarLevelCorrected.lean`**, where `LevelSplit` lives.

It does not permit it, and the invariants force more than `2`: -/

/-- **`2 ≤ S.constr` is intrinsic to `LevelSplit`** — so this module's `hell : 2 ≤ ell` is always
available at the constraint scale, and the gate's coverage concern cannot arise. From
`fibre_pos : 0 < fibre` and `proper : fibre < constr`. -/
theorem levelSplit_two_le_constr (S : CStarLevelCorrected.LevelSplit) : 2 ≤ S.constr := by
  have h1 : 1 ≤ S.fibre := S.fibre_pos
  have h2 : S.fibre < S.constr := S.proper
  omega

/-- Under the target's own `2 ≤ S.fibre`, the constraint scale is strictly larger still. Recorded
because it shows the witness's hypothesis is not merely satisfiable but slack. -/
theorem levelSplit_three_le_constr (S : CStarLevelCorrected.LevelSplit) (hf : 2 ≤ S.fibre) :
    3 ≤ S.constr := by
  have h2 : S.fibre < S.constr := S.proper
  omega

/-- **MUST-FIRE, and it is the whole point.** At `ell = 1` the argument collapses: every site is
coarse, so `coarse_coord_ne_one` has no content and this construction gives nothing. `2 ≤ ell` is
necessary here, not conservative. -/
theorem coarse_coord_ne_one_fails_at_ell_one
    (h : ∀ μ : Fin 3, 4 ≤ L μ) :
    (oneSite h) ∈ CoarseLattice L 1 := by
  rw [mem_CoarseLattice]
  intro μ
  exact Nat.mod_one _

end AdalyFormal.Balaban.LevelTargetWitness
