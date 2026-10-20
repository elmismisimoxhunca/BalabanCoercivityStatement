/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ReparamCDisjoint

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `FullReparamC` — the FULL multi-constraint CMP99b (3.157) reparametrization `C`

`ReparamCSuTwo.reparamCSuTwo` solves ONE coarse-bond constraint `(Q₁(U)B)(c₀) = 0` by adjusting one
dropped fine bond. `ReparamCDisjoint` then settled the assembly question (its GAP 2): at the
CORRECTED dropped bond

    droppedBondLast ell c = (pathSite c.1.1 c.2 (ell - 1), c.2)

the per-coarse-bond constraints **DECOUPLE** — `droppedBondLast_not_reads` says the constraint
functional `L_c` never reads `droppedBondLast ell c'` for `c ≠ c'`. This module builds the
consequence: the full `C` is **POINTWISE**. No ordering, no simultaneous linear solve.

## The construction

    fullC U ell Dinv B̃ b = if ∃ c, b = droppedBondLast ell c then  −Dinv(c)(rest_c(B̃))
                                                              else  B̃ b

with `rest_c := ReparamCSuTwo.restFunctional U ell c (droppedBondLast ell c)` — the part of
`(Q₁(U)B)(c)` that does not read `B` at `c`'s own dropped bond. The dependent `if` is well-defined
because `droppedBondLast` is INJECTIVE in `c` (§1, proved from the two `ReparamCDisjoint` facts
`droppedBondLast_reads_self` and `droppedBondLast_not_reads` — no fresh arithmetic).

## Why the constraint holds at EVERY coarse bond (§4, the headline)

Fix `c`. On every bond `b` that `L_c` READS, `fullC B̃` agrees with the SINGLE-constraint map
`reparamCSuTwo U ell c (droppedBondLast ell c) (Dinv c) B̃` (`fullC_eq_reparamC_on_reads`):

* at `b = droppedBondLast ell c` both are `−Dinv(c)(rest_c B̃)` (needs injectivity);
* at any other read bond `b`, `b` is NOT a dropped bond at all — if `b = droppedBondLast ell c'`
  then `c' ≠ c`, and `L_c` reading it contradicts `droppedBondLast_not_reads`. So `fullC B̃ b = B̃ b`,
  which is what the single-constraint map does on a free bond.

`lineCoarseRestrictCov_congr` (locality) then transfers `ReparamCSuTwo.reparamCSuTwo_constraint`
verbatim, for every `c`. **This is exactly where the decoupling theorem is load-bearing**: with
`ReparamCSuTwo.droppedBond` (offset `0`) the second bullet is FALSE — `ReparamCDisjoint`'s
`droppedBond_couples_witness` is the kernel-checked counterexample — so the argument does not run,
and this is the sense in which the `ell - 1` offset is forced.

## What else is proved

* `fullC_axialGauge` (§5): if `B̃` vanishes on every axial staircase `Γ_{y',x}` then so does
  `fullC B̃` — because `droppedBondLast_not_mem_staircase` puts every corrected dropped bond OFF
  every staircase, so the correction never lands on a gauge-fixed bond. This is (3.157)'s
  `Λ̃ = Λ \ (⋃ Ax(y) ∪ ⋃ B(c)∩c)` disjointness, operationally.
* `fullCLM` (§3): `fullC` is `ℝ`-linear, as a bundled `LinearMap`.
* `fullCLM_ne_zero` (§6): NOT the S91-vacuous `C = 0`. For `ell ≥ 2` and a tiled extent, EVERY bond
  based at a coarse site is a free bond (`coarseBond_base_not_dropped`: a dropped bond sits at
  `μ`-offset `ell - 1 ≢ 0 (mod ell)`), so `fullC` is the identity there. General — no witness
  lattice.
* `fullC_ne_id` (§6b): nor is it the OTHER degenerate map. On a field supported at one dropped bond
  the `b₀`-independent part `rest_c` vanishes, so `fullC` sends it to `0` there — the
  reparametrization genuinely eliminates a variable. This holds for ANY `Dinv`, `hinv` unused.
* §7 (OPS-10, same pass): at `ell = 2` the hypothesis `Dinv` is DISCHARGED. `coeffDc_ell2` computes
  the diagonal coefficient exactly — the only two `(x,i)` terms reaching the dropped bond are
  `(y,1)` and `(y+e_μ,0)` and both carry holonomy `U_μ(y)` (`ReparamCDisjoint.transport_terms_eq`),
  giving `coeffDc = (1/8)·RMap(U_μ(y))`, inverted by `dinvEll2 U c := 8 · RMap(U_μ(y)⁻¹)` with
  `RMap_mul`/`RMap_one`. Hence `fullC_ell2_mem_kerQ` is UNCONDITIONAL: no assumed inverse, no
  numerics, for every `U`, every tiled extent with `2 ∣ L μ + 1`, and every `B̃`.
* §8 (OPS-10, same pass, SUPERSEDING §7's restriction): the SAME discharge for EVERY block size.
  `coeffDc_general` enumerates the contributing terms for general `ell` — exactly one block site per
  `i < ell`, all carrying the SAME transport `dropTransport = U_μ(y)⋯U_μ(y+(ell-2)e_μ)` — giving
  `coeffDc = (1/ell³)·RMap(dropTransport)`, inverted by `dinvC U ell c := ell³ · RMap(dropTransport⁻¹)`.
  `fullC_unconditional_mem_kerQ` therefore holds for every `0 < ell` with `ell ∣ L μ + 1`.
  `coeffDc_ne_zero` (§8d) records that the coefficient is not degenerate.
* §9 (OPS-10, same pass): a NAMED (not existentially quantified) NONZERO element of the (3.157)
  admissible domain, for EVERY `U`. `freeBond ell y` is proved to escape BOTH exclusions —
  `freeBond_not_dropped` (its `1`-coordinate is `≢ 0 mod ell`) and `freeBond_not_mem_staircase` (its
  `0`-coordinate is past the top of every staircase's direction-`0` leg) — so
  `admissibleWitness U ell y := fullC U ell (dinvC U ell) (Pi.single (freeBond ell y) suTwoWitness)`
  satisfies `≠ 0`, `∈ ker Q₁(U)` and "vanishes on every staircase" simultaneously. `2 ≤ ell` is
  load-bearing: at `ell = 1` the two exclusions exhaust the block.

## Scope — what is NOT claimed

* ~~The `ell ≥ 3` diagonal coefficient is NOT computed here. For general `ell` the module carries
  `Dinv` as a hypothesis with the explicit right-inverse condition `hinv`; only `ell = 2` is
  unconditional. Stated honestly: §7's discharge is `ell = 2`-only.~~ **SUPERSEDED in the same pass
  by §8**: the coefficient is now computed for every `ell`, and `dinvC`/`dinvC_hinv` discharge
  `Dinv` unconditionally for every `0 < ell` with `ell ∣ L μ + 1`. §7's `ell = 2` results are kept
  as an INDEPENDENT second derivation (§8e records that the two agree), not as the scope boundary.
  The general theorems still carry the tiling hypothesis `ell ∣ L μ + 1` and `0 < ell`; that is a
  hypothesis of the surrounding `ReparamCDisjoint` development, not a defect introduced here.
* The OFF-diagonal coefficients (the coefficient of a NON-dropped bond in `(Q₁B)(c)`) are not
  computed; nothing here needs them. `restFunctional` is used as an opaque linear functional
  throughout, exactly as in `ReparamCSuTwo`.
* **NO coercivity.** `C*Δ_kC ≥ γ₀` is NOT assembled, and nothing here is claimed about
  `coerc_u_main` or any spine target. **Precision on "the non-vacuity residual"** (these are two
  different statements and §9 settles only the first): (i) *`V(Λ̃)` contains a nonzero vector, for a
  fixed possibly-nontrivial `U`* — DELIVERED by §9 (`admissibleWitness_ne_zero` + `_mem_ker` +
  `_axialGauge`), so a coercivity target over `V(Λ̃)` is not vacuous for lack of any vector to test;
  (ii) *a positive lower bound `γ₀` on the quadratic form over ALL of `V(Λ̃)`, uniform in `k` and
  `U`* — NOT touched here, not even for one `U`. §9 exhibits one member of the domain; it says
  nothing about the form's values, its infimum, or whether the infimum is positive.
* `Q₁(U)` is `LineIntegralCovariant.lineCoarseRestrictCov U ell` throughout, the same faithful
  operator `ReparamCSuTwo`/`ReparamCDisjoint` use (LAW-19); the identification of CMP99b p.428's
  bare `Q` with `Q₁` is `ReparamCSuTwo`'s, inherited, not re-argued here.
-/

namespace AdalyFormal.Balaban.FullReparamC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul_apply suTwoWitness
  suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_ell2 transportPath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.ReparamCSuTwo (restFunctional coeffDc coeffDc_apply reparamCSuTwo
  reparamCSuTwo_at_b0 reparamCSuTwo_free_bond reparamCSuTwo_constraint constraintFunctional
  dropZero dropZero_apply)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_reads_self
  droppedBondLast_not_reads lineCoarseRestrictCov_congr droppedBondLast_not_mem_staircase
  coarse_coord_add_ell_le pathSite_apply_self_val pathSite_apply_ne transport_terms_eq
  staircasePath_base_mem_block)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `droppedBondLast` is INJECTIVE (well-definedness of the dependent `if`) -/

/-- **The corrected dropped bond determines its coarse bond.** Proved from the two bracketing facts
of `ReparamCDisjoint` and nothing else: `L_c` reads its OWN dropped bond
(`droppedBondLast_reads_self`) but reads NO OTHER coarse bond's (`droppedBondLast_not_reads`); so
two coarse bonds with the same dropped bond cannot be distinct. -/
theorem droppedBondLast_injective {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Injective (droppedBondLast (L := L) ell) := by
  intro c c' h
  by_contra hne
  have hself : ReadsBond ell c (droppedBondLast ell c) := droppedBondLast_reads_self hell c
  rw [h] at hself
  exact droppedBondLast_not_reads hell hdvd c c' hne hself

/-- **`IsDropped ell b`** — `b` is the corrected dropped bond of SOME coarse bond, i.e. `b` is one
of the (3.157) variables eliminated by the `Q₁`-constraint rather than a free variable. -/
def IsDropped (ell : ℕ) (b : Bond L) : Prop := ∃ c : CoarseBond L ell, b = droppedBondLast ell c

theorem isDropped_droppedBondLast {ell : ℕ} (c : CoarseBond L ell) :
    IsDropped ell (droppedBondLast ell c) := ⟨c, rfl⟩

/-! ## §2 — the full pointwise (3.157) reparametrization -/

/-- The value the single-`c` constraint forces on `c`'s dropped bond: `−Dinv(c)(rest_c(B̃))`, the
`ReparamCSuTwo` solve pattern retargeted to `droppedBondLast`. -/
noncomputable def solvedValue
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo)
    (c : CoarseBond L ell) : SuTwo :=
  -(Dinv c (restFunctional U ell c (droppedBondLast ell c) B))

/-- **THE FULL (3.157) `C`.** Identity on every free bond; on each dropped bond
`droppedBondLast ell c`, the value solving `c`'s own constraint. Pointwise — the decoupling theorem
of `ReparamCDisjoint` is what makes this legitimate. -/
noncomputable def fullC
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) :
    Bond L → SuTwo :=
  fun b => @dite SuTwo (IsDropped ell b) (Classical.dec _)
    (fun h => solvedValue U ell Dinv B h.choose) (fun _ => B b)

theorem fullC_free
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) {b : Bond L}
    (hb : ¬ IsDropped ell b) : fullC U ell Dinv B b = B b := dif_neg hb

/-- **The value on a dropped bond**, with the coarse bond IDENTIFIED — this is where injectivity
is consumed. -/
theorem fullC_dropped {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo)
    (c : CoarseBond L ell) :
    fullC U ell Dinv B (droppedBondLast ell c) = solvedValue U ell Dinv B c := by
  have h : IsDropped ell (droppedBondLast (L := L) ell c) := isDropped_droppedBondLast c
  have hc : c = h.choose := droppedBondLast_injective hell hdvd h.choose_spec
  show (@dite SuTwo (IsDropped ell (droppedBondLast (L := L) ell c)) (Classical.dec _)
    (fun h => solvedValue U ell Dinv B h.choose) (fun _ => B _)) = _
  rw [dif_pos h, ← hc]

/-! ## §3 — linearity: the bundled `LinearMap` -/

theorem fullC_add
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B₁ B₂ : Bond L → SuTwo) :
    fullC U ell Dinv (B₁ + B₂) = fullC U ell Dinv B₁ + fullC U ell Dinv B₂ := by
  funext b
  by_cases h : IsDropped ell b
  · show (@dite SuTwo (IsDropped ell b) (Classical.dec _) _ _) =
      (@dite SuTwo (IsDropped ell b) (Classical.dec _) _ _) +
      (@dite SuTwo (IsDropped ell b) (Classical.dec _) _ _)
    rw [dif_pos h, dif_pos h, dif_pos h]
    simp only [solvedValue, map_add, neg_add]
  · rw [Pi.add_apply, fullC_free U Dinv _ h, fullC_free U Dinv _ h, fullC_free U Dinv _ h,
      Pi.add_apply]

theorem fullC_smul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (a : ℝ) (B : Bond L → SuTwo) :
    fullC U ell Dinv (a • B) = a • fullC U ell Dinv B := by
  funext b
  by_cases h : IsDropped ell b
  · show (@dite SuTwo (IsDropped ell b) (Classical.dec _) _ _) =
      a • (@dite SuTwo (IsDropped ell b) (Classical.dec _) _ _)
    rw [dif_pos h, dif_pos h]
    simp only [solvedValue, map_smul, smul_neg]
  · rw [Pi.smul_apply, fullC_free U Dinv _ h, fullC_free U Dinv _ h, Pi.smul_apply]

/-- **`fullC` is a genuine `ℝ`-linear operator** on bond fields. -/
noncomputable def fullCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) where
  toFun := fullC U ell Dinv
  map_add' := fullC_add U Dinv
  map_smul' := fullC_smul U Dinv

theorem fullCLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) :
    fullCLM U ell Dinv B = fullC U ell Dinv B := rfl

/-! ## §4 — THE HEADLINE: `fullC B̃ ∈ ker Q₁(U)`, at EVERY coarse bond -/

/-- **The decoupling, consumed.** On every bond that the constraint at `c` READS, the full `C`
agrees with the single-constraint map for `c`. The `b ≠ b₀` case is exactly
`droppedBondLast_not_reads`. -/
theorem fullC_eq_reparamC_on_reads {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo)
    (c : CoarseBond L ell) (b : Bond L) (hb : ReadsBond ell c b) :
    fullC U ell Dinv B b =
      reparamCSuTwo U ell c (droppedBondLast ell c) (Dinv c) B b := by
  by_cases hbb : b = droppedBondLast ell c
  · subst hbb
    rw [fullC_dropped hell hdvd U Dinv B c, reparamCSuTwo_at_b0]
    rfl
  · have hfree : ¬ IsDropped ell b := by
      rintro ⟨c', rfl⟩
      have hne : c ≠ c' := by
        rintro rfl
        exact hbb rfl
      exact droppedBondLast_not_reads hell hdvd c c' hne hb
    rw [fullC_free U Dinv B hfree, reparamCSuTwo_free_bond U ell c _ (Dinv c) B hbb]

/-- **`fullC B̃ ∈ ker Q₁(U)` — the (3.157) constraint at EVERY coarse bond, simultaneously.**

Given a per-coarse-bond right inverse `Dinv c` of the diagonal coefficient `coeffDc` at `c`'s own
dropped bond, the pointwise `fullC` satisfies `(Q₁(U)(C B̃))(c) = 0` for every `c` and every `B̃`.

There is no ordering and no simultaneous solve: the proof rewrites `L_c(fullC B̃)` into
`L_c(reparamCSuTwo … c …  B̃)` by locality (`lineCoarseRestrictCov_congr`) and then quotes the
single-constraint theorem. -/
theorem fullC_mem_kerQ {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (B : Bond L → SuTwo) :
    ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell (fullC U ell Dinv B) c = 0 := by
  intro c
  rw [lineCoarseRestrictCov_congr U ell (fullC U ell Dinv B)
      (reparamCSuTwo U ell c (droppedBondLast ell c) (Dinv c) B) c
      (fun b hb => fullC_eq_reparamC_on_reads hell hdvd U Dinv B c b hb)]
  exact reparamCSuTwo_constraint U ell c (droppedBondLast ell c) (Dinv c) (hinv c) B

/-- **The same statement as literal kernel membership** — so the name `mem_kerQ` is not doing work
the type does not do. `Q₁(U) = lineCoarseRestrictCovLM U ell` and `fullC B̃ ∈ ker Q₁(U)`. -/
theorem fullC_mem_ker {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (B : Bond L → SuTwo) :
    fullC U ell Dinv B ∈ LinearMap.ker (lineCoarseRestrictCovLM U ell) := by
  rw [LinearMap.mem_ker]
  funext c
  rw [Pi.zero_apply, lineCoarseRestrictCovLM_apply]
  exact fullC_mem_kerQ hell hdvd U Dinv hinv B c

/-! ## §5 — the axial gauge is preserved: the correction never lands on a staircase -/

/-- **`fullC` preserves the axial gauge.** If `B̃` vanishes on every staircase `Γ_{y',x}`
(`y'` coarse, `x ∈ B(y')`), so does `fullC B̃`. The corrected dropped bonds lie OFF every staircase
(`ReparamCDisjoint.droppedBondLast_not_mem_staircase`), so `fullC` is the IDENTITY on every
staircase bond — the (3.157) disjointness `Ax(y) ∩ (B(c)∩c) = ∅`, operationally. -/
theorem fullC_axialGauge {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo)
    (hB : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, B e = 0) :
    ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, fullC U ell Dinv B e = 0 := by
  intro y' hy' x hx e he
  have hfree : ¬ IsDropped ell e := by
    rintro ⟨c, rfl⟩
    exact droppedBondLast_not_mem_staircase hell hdvd c y' hy' x hx he
  rw [fullC_free U Dinv B hfree]
  exact hB y' hy' x hx e he

/-! ## §6 — NON-TRIVIALITY: `fullC` is the identity on a genuinely nonempty set of free bonds -/

/-- **Every bond based at a coarse site is FREE**, for `ell ≥ 2` on a tiled extent: a dropped bond
sits at `μ`-offset `ell - 1` from its coarse site and `0 < ell - 1 < ell`, so its base coordinate is
NOT a multiple of `ell`. (This is the general, witness-free non-vacuity statement; the offset
`ell - 1` is again load-bearing — at offset `0` the claim is false by inspection.) -/
theorem coarseBond_base_not_dropped {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    ¬ IsDropped ell ((y, μ) : Bond L) := by
  rintro ⟨c, hc⟩
  simp only [droppedBondLast, Prod.mk.injEq] at hc
  obtain ⟨hsite, -⟩ := hc
  have hfit : (c.1.1 c.2).val + ell ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  have hval : (y c.2).val = ((c.1.1 c.2).val + (ell - 1)) % (L c.2 + 1) := by
    have h1 := congrArg (fun z : PeriodicLatticeSite L => (z c.2).val) hsite
    rwa [pathSite_apply_self_val] at h1
  rw [Nat.mod_eq_of_lt (show (c.1.1 c.2).val + (ell - 1) < L c.2 + 1 by omega)] at hval
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 c.2)
  have hy0 : (y c.2).val % ell = 0 := mem_CoarseLattice.mp hy c.2
  rw [hval, hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (show ell - 1 < ell by omega)] at hy0
  omega

/-- The origin is a coarse site. -/
theorem originSite_coarse {ell : ℕ} :
    (fun _ => 0 : PeriodicLatticeSite L) ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  exact Nat.zero_mod ell

/-- **`fullC ≠ 0` — it is NOT the S91-vacuous `C = 0`.** For `ell ≥ 2` on a tiled extent the bond
`(0, 0)` (origin, direction `0`) is free, so `fullC` acts on it as the identity and maps a field
supported there to a nonzero field. General: no witness lattice, any `U`, any `Dinv`. -/
theorem fullCLM_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    fullCLM U ell Dinv ≠ 0 := by
  intro hzero
  set b₀ : Bond L := ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) with hb₀
  have hfree : ¬ IsDropped ell b₀ :=
    coarseBond_base_not_dropped hell2 hdvd _ originSite_coarse 0
  have hval : fullC U ell Dinv (Pi.single b₀ suTwoWitness) b₀ = suTwoWitness := by
    rw [fullC_free U Dinv _ hfree, Pi.single_eq_same]
  have hz : fullC U ell Dinv (Pi.single b₀ suTwoWitness) = 0 := by
    have := LinearMap.congr_fun hzero (Pi.single b₀ suTwoWitness)
    rwa [fullCLM_apply] at this
  rw [hz] at hval
  exact suTwoWitness_ne_zero hval.symm

/-! ### §6b — `fullC` is not secretly the IDENTITY either

`fullCLM_ne_zero` rules out the S91-vacuous `C = 0`. The opposite degeneracy — a `C` that imposes
nothing, i.e. `C = id` — is ruled out here: on the field supported at a single dropped bond, the
`b₀`-independent part `rest_c` vanishes identically, so `fullC` sends that field to `0` there while
the input is nonzero. So `fullC` genuinely CONSTRAINS, for every `Dinv` whatsoever (the argument
does not even use `hinv`). Together the two theorems bracket `fullC` away from both trivial maps. -/

theorem dropZero_single (b₀ : Bond L) (w : SuTwo) :
    dropZero b₀ (Pi.single b₀ w) = 0 := by
  funext b
  rw [dropZero_apply, Pi.zero_apply]
  by_cases h : b = b₀
  · rw [if_pos h]
  · rw [if_neg h, Pi.single_eq_of_ne h]

theorem restFunctional_single_self
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (w : SuTwo) :
    restFunctional U ell c (droppedBondLast ell c)
      (Pi.single (droppedBondLast ell c) w) = 0 := by
  show constraintFunctional U ell c (dropZero (droppedBondLast ell c)
    (Pi.single (droppedBondLast ell c) w)) = 0
  rw [dropZero_single, map_zero]

/-- **`fullC ≠ id`**: the (3.157) reparametrization genuinely eliminates a variable. -/
theorem fullC_ne_id {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (c : CoarseBond L ell) :
    fullC U ell Dinv (Pi.single (droppedBondLast ell c) suTwoWitness)
      ≠ Pi.single (droppedBondLast ell c) suTwoWitness := by
  intro h
  have h1 := congrFun h (droppedBondLast ell c)
  rw [fullC_dropped hell hdvd U Dinv _ c, solvedValue, restFunctional_single_self, map_zero,
    neg_zero, Pi.single_eq_same] at h1
  exact suTwoWitness_ne_zero h1.symm

theorem fullCLM_ne_id {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    fullCLM U ell Dinv ≠ LinearMap.id := by
  intro h
  set c : CoarseBond L ell := (⟨fun _ => 0, originSite_coarse⟩, 0) with hc
  refine fullC_ne_id hell hdvd U Dinv c ?_
  have := LinearMap.congr_fun h (Pi.single (droppedBondLast ell c) suTwoWitness)
  rwa [fullCLM_apply, LinearMap.id_apply] at this

/-! ## §7 — `ell = 2`: the coefficient `Dinv` is DISCHARGED, so `fullC` is UNCONDITIONAL

At `ell = 2` exactly two `(x,i)` terms of the `Q₁`-block-sum reach `droppedBondLast 2 c`, and both
carry holonomy `U_μ(y)`; this section turns that into the operator identity
`coeffDc U 2 c (droppedBondLast 2 c) = (1/8)·RMap(U_μ(y))`, which `RMap_mul`/`RMap_one` invert.

**What `coeffDc_ell2`'s proof actually uses** (stated precisely, because a citation that the proof
does not consume is worse than no citation): `Q1Real.rZeroA_ell2` (the two-term unfold of `rZeroA` at
`ell = 2`) and `ReparamCDisjoint.transport_terms_eq` (the two holonomies coincide, and this DOES
carry `gammaPath_shift`'s side condition `0 < L μ`, supplied here by `pos_L_of_two_dvd`), plus its
OWN inline uniqueness arguments — a `Finset.sum_eq_single` in each of the two sums, with the
"no other block site contributes" step proved in place. `ReparamCDisjoint.readers_ell2` states the
same enumeration fact and is NOT invoked by this proof; it is an independent statement of it.

**STATUS: this section is no longer the scope boundary.** §8 below discharges `Dinv` for EVERY
`ell`, by an independent enumeration that never touches `readers_ell2`/`transport_terms_eq`. §7 is
retained deliberately as a SECOND, de-correlated derivation of the same coefficient; §8e
(`coeffDc_ell2_eq_general`, `dinvEll2_eq_dinvC`) records that the two agree. Downstream code should
prefer §8's `dinvC`; `dinvEll2` is kept only for that cross-check. -/

theorem pathSite_one (x : PeriodicLatticeSite L) (μ : Fin 3) :
    pathSite x μ 1 = periodicLatticeShift x μ := by
  rw [pathSite_succ, pathSite_zero]

/-- On a tiled extent with `ell = 2` no direction is degenerate (`L μ = 0` would give `2 ∣ 1`).
This is the side condition `ReparamCDisjoint.gammaPath_shift` carries. -/
theorem pos_L_of_two_dvd (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (μ : Fin 3) : 0 < L μ := by
  obtain ⟨k, hk⟩ := hdvd μ
  omega

theorem shift_val_of_lt {x : PeriodicLatticeSite L} {μ : Fin 3} (h : (x μ).val + 1 < L μ + 1) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
  rw [← pathSite_one, pathSite_apply_self_val]
  exact Nat.mod_eq_of_lt h

theorem shift_apply_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    (periodicLatticeShift x μ) ν = x ν := by
  rw [← pathSite_one]
  exact pathSite_apply_ne x μ ν 1 h

/-- The dropped bond at `ell = 2` is the bond based at the `μ`-neighbour of the coarse site. -/
theorem droppedBondLast_two (c : CoarseBond L 2) :
    droppedBondLast 2 c = ((periodicLatticeShift c.1.1 c.2, c.2) : Bond L) := by
  simp only [droppedBondLast]
  rw [show (2 : ℕ) - 1 = 1 from rfl, pathSite_one]

/-- **The diagonal coefficient at `ell = 2`, computed exactly.** Only `(x,i) = (y,1)` and
`(y+e_μ,0)` reach the dropped bond, both with transport holonomy `U_μ(y)`; with the `1/ell⁴ = 1/16`
prefactor the coefficient is `(1/8)·RMap(U_μ(y))`. No numerics. -/
theorem coeffDc_ell2 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 2) (v : SuTwo) :
    coeffDc U 2 c (droppedBondLast 2 c) v = (1 / 8 : ℝ) • RMap (U (c.1.1, c.2)) v := by
  have hL : 0 < L c.2 := pos_L_of_two_dvd hdvd c.2
  have hfit : (c.1.1 c.2).val + 2 ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  set y : PeriodicLatticeSite L := c.1.1 with hy
  set μ : Fin 3 := c.2 with hμ
  set z : PeriodicLatticeSite L := periodicLatticeShift y μ with hz
  have hzμ : (z μ).val = (y μ).val + 1 := shift_val_of_lt (by omega)
  have hz_mem : z ∈ blockOf y 2 := by
    rw [mem_blockOf]
    intro ν
    rcases eq_or_ne ν μ with rfl | hν
    · omega
    · rw [hz, shift_apply_ne y μ ν hν]; omega
  have hy_mem : y ∈ blockOf y 2 := by
    rw [mem_blockOf]; intro ν; omega
  rw [coeffDc_apply, droppedBondLast_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) •
      ∑ x ∈ blockOf y 2, rZeroA U y x (Pi.single ((z, μ) : Bond L) v) μ 2 = _
  have hsplit : ∀ x ∈ blockOf y 2,
      rZeroA U y x (Pi.single ((z, μ) : Bond L) v) μ 2 =
        RMap (periodicPathHolonomy U y (transportPath y x μ 0))
          ((Pi.single ((z, μ) : Bond L) v : Bond L → SuTwo) (x, μ)) +
        RMap (periodicPathHolonomy U y (transportPath y x μ 1))
          ((Pi.single ((z, μ) : Bond L) v : Bond L → SuTwo) (periodicLatticeShift x μ, μ)) :=
    fun x _ => rZeroA_ell2 U y x _ μ
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the `i = 0` sum: only `x = z` contributes
  have hsum0 : ∑ x ∈ blockOf y 2,
      RMap (periodicPathHolonomy U y (transportPath y x μ 0))
        ((Pi.single ((z, μ) : Bond L) v : Bond L → SuTwo) (x, μ)) = RMap (U (y, μ)) v := by
    rw [Finset.sum_eq_single z]
    · rw [Pi.single_eq_same, hz, (transport_terms_eq U y μ hL).2]
    · intro x _ hx
      have hne : ((x, μ) : Bond L) ≠ (z, μ) := fun h => hx (congrArg Prod.fst h)
      rw [Pi.single_eq_of_ne hne, map_zero]
    · intro h; exact absurd hz_mem h
  -- the `i = 1` sum: only `x = y` contributes
  have hsum1 : ∑ x ∈ blockOf y 2,
      RMap (periodicPathHolonomy U y (transportPath y x μ 1))
        ((Pi.single ((z, μ) : Bond L) v : Bond L → SuTwo) (periodicLatticeShift x μ, μ))
      = RMap (U (y, μ)) v := by
    rw [Finset.sum_eq_single y]
    · rw [← hz, Pi.single_eq_same, (transport_terms_eq U y μ hL).1]
    · intro x hx hxy
      have hshift_ne : periodicLatticeShift x μ ≠ z := by
        intro hcontra
        apply hxy
        rw [mem_blockOf] at hx
        have hxμ : (x μ).val = (y μ).val := by
          have hvv : ((periodicLatticeShift x μ) μ).val = (z μ).val := by rw [hcontra]
          rw [← pathSite_one, pathSite_apply_self_val, hzμ] at hvv
          rcases (show (x μ).val = (y μ).val ∨ (x μ).val = (y μ).val + 1 by
              have := hx μ; omega) with h | h
          · exact h
          · exfalso
            rw [h] at hvv
            rcases eq_or_lt_of_le hfit with heq | hlt
            · rw [show (y μ).val + 1 + 1 = L μ + 1 by omega, Nat.mod_self] at hvv; omega
            · rw [Nat.mod_eq_of_lt (by omega)] at hvv; omega
        funext ν
        rcases eq_or_ne ν μ with rfl | hν
        · exact Fin.ext hxμ
        · have h1 : (periodicLatticeShift x μ) ν = z ν := by rw [hcontra]
          rwa [shift_apply_ne x μ ν hν, hz, shift_apply_ne y μ ν hν] at h1
      have hne : ((periodicLatticeShift x μ, μ) : Bond L) ≠ (z, μ) :=
        fun h => hshift_ne (congrArg Prod.fst h)
      rw [Pi.single_eq_of_ne hne, map_zero]
    · intro h; exact absurd hy_mem h
  rw [hsum0, hsum1, ← two_smul ℝ, smul_smul]
  norm_num

/-- The operator form of `coeffDc_ell2`. Provided for downstream consumers (parity with §8d's
`coeffDc_general_op`); NOT consumed inside this file — `dinvEll2_hinv` uses the pointwise
`coeffDc_ell2` directly. Axiom-checked below so it is not unverified dead weight. -/
theorem coeffDc_ell2_op (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 2) :
    coeffDc U 2 c (droppedBondLast 2 c) = (1 / 8 : ℝ) • RMap (U (c.1.1, c.2)) := by
  ext v
  rw [coeffDc_ell2 hdvd U c v]
  simp

/-- **The explicit inverse at `ell = 2`**: `8 · RMap(U_μ(y)⁻¹)`. -/
noncomputable def dinvEll2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 2) : SuTwo →ₗ[ℝ] SuTwo :=
  (8 : ℝ) • RMap (U (c.1.1, c.2))⁻¹

/-- **`hinv` DISCHARGED at `ell = 2`, for every `U` and every tiled extent.** -/
theorem dinvEll2_hinv (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 2) :
    (coeffDc U 2 c (droppedBondLast 2 c)).comp (dinvEll2 U c) = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, dinvEll2]
  simp only [LinearMap.smul_apply, map_smul]
  rw [coeffDc_ell2 hdvd U c, RMap_mul_apply, mul_inv_cancel, RMap_one]
  simp only [LinearMap.id_apply, smul_smul]
  norm_num

/-- **THE FULL (3.157) `C`, UNCONDITIONAL AT `ell = 2`.** No assumed inverse: for every `U`, every
extent with `2 ∣ L μ + 1`, and every `B̃`, the pointwise `fullC U 2 (dinvEll2 U) B̃` satisfies the
covariant constraint `(Q₁(U)(C B̃))(c) = 0` at EVERY coarse bond `c` simultaneously. -/
theorem fullC_ell2_mem_kerQ (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) :
    ∀ c : CoarseBond L 2,
      lineCoarseRestrictCov U 2 (fullC U 2 (dinvEll2 U) B) c = 0 :=
  fullC_mem_kerQ (by norm_num) hdvd U (dinvEll2 U) (dinvEll2_hinv hdvd U) B

/-- The `ell = 2` axial-gauge preservation, with the inverse discharged. -/
theorem fullC_ell2_axialGauge (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo)
    (hB : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' 2 →
      ∀ e ∈ staircasePath y' x, B e = 0) :
    ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' 2 →
      ∀ e ∈ staircasePath y' x, fullC U 2 (dinvEll2 U) B e = 0 :=
  fullC_axialGauge (by norm_num) hdvd U (dinvEll2 U) B hB

/-- The `ell = 2` non-triviality, with the inverse discharged. -/
theorem fullCLM_ell2_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    fullCLM U 2 (dinvEll2 U) ≠ 0 :=
  fullCLM_ne_zero (by norm_num) hdvd U (dinvEll2 U)

/-! ## §8 — GENERAL `ell`: the diagonal coefficient computed for EVERY block size

§7 discharged `Dinv` only at `ell = 2`, by quoting `ReparamCDisjoint` §5d's two-term enumeration.
This section removes that restriction. The mechanism is the same but the enumeration is done for
general `ell`: for each `i < ell` there is EXACTLY ONE block site reaching the dropped bond, namely
`x_i = pathSite y μ (ell-1-i)` (§8b), and the transport path of that term is

    Γ_{y,x_i} ++ [x_i → x_i + i·e_μ] = replicate (ell-1-i) (μ,true) ++ replicate i (μ,true)
                                     = replicate (ell-1) (μ,true),

**independent of `i`** (§8a–§8c). So all `ell` contributions carry the SAME holonomy
`dropTransport = U_μ(y)·U_μ(y+e_μ)⋯U_μ(y+(ell-2)e_μ)` — the parallel transport from the coarse site
along `c` to the dropped bond's base — and

    coeffDc U ell c (droppedBondLast ell c) = (ell / ell⁴) · RMap(dropTransport) = (1/ell³)·RMap(…),

invertible by `RMap_mul`/`RMap_one`. §7's `ell = 2` value `(1/8)·RMap(U_μ(y))` is recovered as the
cross-check `coeffDc_ell2_eq_general` (§8e) — two independently-derived computations of the same
coefficient, one via `ReparamCDisjoint.readers_ell2`/`transport_terms_eq`, one via §8's general
enumeration. -/

/-! ### §8a — closed forms for `pathSite`, `GammaPath` and `straightSegment` along one axis -/

theorem pathSite_add (x : PeriodicLatticeSite L) (μ : Fin 3) (a b : ℕ) :
    pathSite (pathSite x μ a) μ b = pathSite x μ (a + b) := by
  induction b with
  | zero => rw [pathSite_zero, Nat.add_zero]
  | succ b ih =>
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      rw [pathSite_succ, ih, hab, pathSite_succ]

theorem coordSteps_pathSite_self (y : PeriodicLatticeSite L) (μ : Fin 3) (m : ℕ)
    (hm : m < L μ + 1) : Q1Real.coordSteps y (pathSite y μ m) μ = m := by
  simp only [Q1Real.coordSteps, AdalyFormal.Balaban.ReparamCDisjoint.pathSite_eq,
    Function.update_self, add_sub_cancel_left]
  rw [AdalyFormal.Balaban.Q1Real.nsmul_one_val]
  exact Nat.mod_eq_of_lt hm

theorem coordSteps_pathSite_ne (y : PeriodicLatticeSite L) (μ ν : Fin 3) (m : ℕ) (h : ν ≠ μ) :
    Q1Real.coordSteps y (pathSite y μ m) ν = 0 := by
  simp only [Q1Real.coordSteps, pathSite_apply_ne y μ ν m h, sub_self, Fin.val_zero]

/-- Each of `GammaPath`'s three legs, for a target displaced from `y` along a single axis. -/
theorem leg_eq_pathSite (y : PeriodicLatticeSite L) (μ d : Fin 3) (m : ℕ) (hm : m < L μ + 1)
    (base : PeriodicLatticeSite L) (hb : base d = y d) :
    Q1Real.straightSegment base (pathSite y μ m) d =
      if d = μ then List.replicate m (μ, true) else [] := by
  have hc : Q1Real.coordSteps base (pathSite y μ m) d
      = Q1Real.coordSteps y (pathSite y μ m) d := by
    simp only [Q1Real.coordSteps, hb]
  simp only [Q1Real.straightSegment, hc]
  rcases eq_or_ne d μ with rfl | h
  · rw [coordSteps_pathSite_self y d m hm, if_pos rfl]
  · rw [coordSteps_pathSite_ne y μ d m h, if_neg h, List.replicate_zero]

/-- **`Γ_{y, y + m·e_μ}` is the straight `m`-step run** — the coarse-to-block contour to a site
displaced along a single axis does not detour. Generalizes `ReparamCDisjoint.gammaPath_shift`
(the `m = 1` case). -/
theorem gammaPath_pathSite (y : PeriodicLatticeSite L) (μ : Fin 3) (m : ℕ) (hm : m < L μ + 1) :
    Q1Real.GammaPath y (pathSite y μ m) = List.replicate m (μ, true) := by
  have hb1 : (Function.update y 2 ((pathSite y μ m) 2)) 1 = y 1 :=
    Function.update_of_ne (by decide) _ _
  have hb0 : (Function.update (Function.update y 2 ((pathSite y μ m) 2)) 1
      ((pathSite y μ m) 1)) 0 = y 0 := by
    rw [Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
  unfold Q1Real.GammaPath
  rw [leg_eq_pathSite y μ 2 m hm y rfl, leg_eq_pathSite y μ 1 m hm _ hb1,
    leg_eq_pathSite y μ 0 m hm _ hb0]
  have hμ : μ = 0 ∨ μ = 1 ∨ μ = 2 := by
    rcases μ with ⟨w, hw⟩
    match w, hw with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr (Or.inl rfl)
    | 2, _ => exact Or.inr (Or.inr rfl)
  rcases hμ with rfl | rfl | rfl <;> simp

theorem straightSegment_pathSite (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ)
    (hi : i < L μ + 1) :
    Q1Real.straightSegment x (pathSite x μ i) μ = List.replicate i (μ, true) := by
  simp only [Q1Real.straightSegment, coordSteps_pathSite_self x μ i hi]

/-! ### §8b — the transport path of every contributing term is the SAME -/

/-- **The parallel transport along the long bond `c`, from its coarse base to the dropped bond's
base**: the ordered product `U_μ(y)·U_μ(y+e_μ)⋯U_μ(y+(ell-2)e_μ)`, i.e. the holonomy of the
`(ell-1)`-step run in direction `μ`. -/
noncomputable def dropTransport
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  periodicPathHolonomy U c.1.1 (List.replicate (ell - 1) (c.2, true))

/-- **`i`-INDEPENDENCE of the transport factor.** The term `(x_i, i)` with
`x_i = pathSite y μ (ell-1-i)` carries transport path `replicate (ell-1) (μ,true)` for EVERY
`i < ell`. This is what collapses the `ell` contributions into a single scalar multiple. -/
theorem transportPath_hit (y : PeriodicLatticeSite L) (μ : Fin 3) (ell i : ℕ)
    (hi : i < ell) (hle : ell ≤ L μ + 1) :
    transportPath y (pathSite y μ (ell - 1 - i)) μ i = List.replicate (ell - 1) (μ, true) := by
  have h1 : ell - 1 - i < L μ + 1 := by omega
  have h2 : i < L μ + 1 := by omega
  rw [transportPath, gammaPath_pathSite y μ (ell - 1 - i) h1,
    straightSegment_pathSite _ μ i h2, ← List.replicate_add]
  congr 1
  omega

/-! ### §8c — the exact enumeration: one contributing site per `i` -/

theorem pathSite_mem_block {ell : ℕ} (hell : 0 < ell) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (m : ℕ) (hm : m < ell) (hfit : (y μ).val + ell ≤ L μ + 1) :
    pathSite y μ m ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro ν
  rcases eq_or_ne ν μ with rfl | hν
  · rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [pathSite_apply_ne y μ ν m hν]; exact ⟨le_refl _, by have := hell; omega⟩

/-- **Uniqueness**: inside the block, `pathSite x μ i = pathSite y μ (ell-1)` forces
`x = pathSite y μ (ell-1-i)`. The periodic-wraparound branch is arithmetically impossible because
the block fits (`(y μ).val + ell ≤ L μ + 1`). -/
theorem hit_unique {ell : ℕ} (hell : 0 < ell) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (hfit : (y μ).val + ell ≤ L μ + 1) (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (i : ℕ) (hi : i < ell) (heq : pathSite x μ i = pathSite y μ (ell - 1)) :
    x = pathSite y μ (ell - 1 - i) := by
  rw [mem_blockOf] at hx
  have hxlo := (hx μ).1
  have hxhi := (hx μ).2
  have hval : ((x μ).val + i) % (L μ + 1) = ((y μ).val + (ell - 1)) % (L μ + 1) := by
    have h1 := congrArg (fun z : PeriodicLatticeSite L => (z μ).val) heq
    rwa [pathSite_apply_self_val, pathSite_apply_self_val] at h1
  rw [Nat.mod_eq_of_lt (show (y μ).val + (ell - 1) < L μ + 1 by omega)] at hval
  have hsum : (x μ).val + i = (y μ).val + (ell - 1) := by
    rcases lt_or_ge ((x μ).val + i) (L μ + 1) with hlt | hge
    · rwa [Nat.mod_eq_of_lt hlt] at hval
    · exfalso
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt (show (x μ).val + i - (L μ + 1) < L μ + 1 by omega)] at hval
      omega
  funext ν
  rcases eq_or_ne ν μ with rfl | hν
  · apply Fin.ext
    rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [pathSite_apply_ne y μ ν _ hν]
    have h1 := congrFun heq ν
    rwa [pathSite_apply_ne x μ ν i hν, pathSite_apply_ne y μ ν _ hν] at h1

/-! ### §8d — the coefficient, and the DISCHARGED inverse, for every `ell` -/

/-- **THE DIAGONAL COEFFICIENT, GENERAL `ell`.** `coeffDc` at `c`'s own corrected dropped bond is
`(1/ell³)·RMap(dropTransport)`. Derived, not assumed: `ell` terms of the block double-sum reach the
dropped bond (one per `i < ell`, `hit_unique`), all with the same transport (`transportPath_hit`),
against the `1/ell⁴` prefactor. -/
theorem coeffDc_general {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L ell) (v : SuTwo) :
    coeffDc U ell c (droppedBondLast ell c) v
      = (1 / (ell : ℝ) ^ 3) • RMap (dropTransport U ell c) v := by
  have hfit : (c.1.1 c.2).val + ell ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  have hle : ell ≤ L c.2 + 1 := by omega
  rw [coeffDc_apply]
  show (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf c.1.1 ell,
      rZeroA U c.1.1 x (Pi.single (droppedBondLast ell c) v) c.2 ell = _
  simp only [rZeroA]
  rw [Finset.sum_comm]
  have hinner : ∀ i ∈ Finset.range ell,
      ∑ x ∈ blockOf c.1.1 ell,
        RMap (periodicPathHolonomy U c.1.1 (transportPath c.1.1 x c.2 i))
          ((Pi.single (droppedBondLast ell c) v : Bond L → SuTwo) (pathSite x c.2 i, c.2))
        = RMap (dropTransport U ell c) v := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.sum_eq_single (pathSite c.1.1 c.2 (ell - 1 - i))]
    · have hsite : pathSite (pathSite c.1.1 c.2 (ell - 1 - i)) c.2 i
          = pathSite c.1.1 c.2 (ell - 1) := by
        rw [pathSite_add]
        congr 1
        omega
      have hhit : ((pathSite (pathSite c.1.1 c.2 (ell - 1 - i)) c.2 i, c.2) : Bond L)
          = droppedBondLast ell c := by
        rw [droppedBondLast, hsite]
      rw [hhit, Pi.single_eq_same, transportPath_hit c.1.1 c.2 ell i hi hle, dropTransport]
    · intro x hx hxne
      have hne : ((pathSite x c.2 i, c.2) : Bond L) ≠ droppedBondLast ell c := by
        intro hcontra
        simp only [droppedBondLast, Prod.mk.injEq] at hcontra
        exact hxne (hit_unique hell c.1.1 c.2 hfit x hx i hi hcontra.1)
      rw [Pi.single_eq_of_ne hne, map_zero]
    · intro h
      exact absurd (pathSite_mem_block hell c.1.1 c.2 (ell - 1 - i) (by omega) hfit) h
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  congr 1
  field_simp

theorem coeffDc_general_op {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L ell) :
    coeffDc U ell c (droppedBondLast ell c) = (1 / (ell : ℝ) ^ 3) • RMap (dropTransport U ell c) := by
  ext v
  rw [coeffDc_general hell hdvd U c v]
  simp

/-- **The explicit inverse, general `ell`**: `ell³ · RMap(dropTransport⁻¹)`. -/
noncomputable def dinvC
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) : SuTwo →ₗ[ℝ] SuTwo :=
  ((ell : ℝ) ^ 3) • RMap (dropTransport U ell c)⁻¹

/-- **`hinv` DISCHARGED for EVERY `ell > 0`**, every `U`, every tiled extent. -/
theorem dinvC_hinv {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L ell) :
    (coeffDc U ell c (droppedBondLast ell c)).comp (dinvC U ell c) = LinearMap.id := by
  have hne : ((ell : ℝ) ^ 3) ≠ 0 := pow_ne_zero 3 (Nat.cast_ne_zero.mpr (by omega))
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, dinvC]
  simp only [LinearMap.smul_apply, map_smul]
  rw [coeffDc_general hell hdvd U c, RMap_mul_apply, mul_inv_cancel, RMap_one]
  simp only [LinearMap.id_apply, smul_smul, mul_one_div, div_self hne, one_smul]

/-- **The coefficient is NOT degenerate.** If `coeffDc` at the dropped bond were `0`, the (3.157)
equation "considered as an equation on the variable `B(b₀)`" would not determine `B(b₀)` at all and
the whole construction would be empty. It is nonzero — immediately from the discharged `hinv`
together with `SuTwo ≠ 0`. -/
theorem coeffDc_ne_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L ell) : coeffDc U ell c (droppedBondLast ell c) ≠ 0 := by
  intro h0
  have hid := dinvC_hinv hell hdvd U c
  rw [h0, LinearMap.zero_comp] at hid
  have h1 := LinearMap.congr_fun hid suTwoWitness
  rw [LinearMap.zero_apply, LinearMap.id_apply] at h1
  exact suTwoWitness_ne_zero h1.symm

/-- **THE FULL (3.157) `C`, UNCONDITIONAL FOR EVERY BLOCK SIZE.** No assumed inverse and no `ell`
restriction beyond `0 < ell` and the tiling `ell ∣ L μ + 1`: for every `U` and every `B̃`,
`fullC U ell (dinvC U ell) B̃` satisfies `(Q₁(U)(C B̃))(c) = 0` at EVERY coarse bond `c`
simultaneously. -/
theorem fullC_unconditional_mem_kerQ {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) :
    ∀ c : CoarseBond L ell,
      lineCoarseRestrictCov U ell (fullC U ell (dinvC U ell) B) c = 0 :=
  fullC_mem_kerQ hell hdvd U (dinvC U ell) (dinvC_hinv hell hdvd U) B

theorem fullC_unconditional_axialGauge {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo)
    (hB : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, B e = 0) :
    ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, fullC U ell (dinvC U ell) B e = 0 :=
  fullC_axialGauge hell hdvd U (dinvC U ell) B hB

theorem fullCLM_unconditional_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    fullCLM U ell (dinvC U ell) ≠ 0 :=
  fullCLM_ne_zero hell2 hdvd U (dinvC U ell)

/-! ### §8e — CROSS-CHECK: §7's independent `ell = 2` computation agrees with §8's general one

§7 computed the `ell = 2` coefficient through `Q1Real.rZeroA_ell2` (the two-term unfold) plus
`ReparamCDisjoint.transport_terms_eq` (both holonomies `= U_μ(y)`), with its own inline
`Finset.sum_eq_single` uniqueness steps. §8 computed it by its own `gammaPath_pathSite`/`hit_unique`
enumeration, using neither `rZeroA_ell2` nor `transport_terms_eq`. The two derivations share no
lemma beyond `coeffDc_apply` and the definition of `lineCoarseRestrictCov`; this theorem records
that they produce the SAME operator. (A factor-count or orientation error in §8's path lemmas would
make `coeffDc_general` itself unprovable, since both sides are pinned to the same `coeffDc`.) -/
theorem coeffDc_ell2_eq_general (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 2) (v : SuTwo) :
    (1 / 8 : ℝ) • RMap (U (c.1.1, c.2)) v
      = (1 / ((2 : ℕ) : ℝ) ^ 3) • RMap (dropTransport U 2 c) v := by
  rw [← coeffDc_ell2 hdvd U c v, coeffDc_general (by norm_num) hdvd U c v]

/-- The two inverses coincide at `ell = 2`: `dinvEll2 = dinvC … 2`. -/
theorem dinvEll2_eq_dinvC (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 2) : dinvEll2 U c = dinvC U 2 c := by
  have hdt : dropTransport U 2 c = U (c.1.1, c.2) := by
    rw [dropTransport, show (2 : ℕ) - 1 = 1 from rfl, List.replicate_one]
    exact AdalyFormal.Balaban.ReparamCDisjoint.holonomy_singleStep U c.1.1 c.2
  rw [dinvEll2, dinvC, hdt]
  norm_num

/-! ## §9 — A NAMED NONZERO ELEMENT OF THE (3.157) ADMISSIBLE DOMAIN, for EVERY `U`

Everything above says what `fullC` DOES. This section says the resulting subspace is not empty of
content: it exhibits, by name and for every background `U`, a bond field that

  * is nonzero (`admissibleWitness_ne_zero`),
  * satisfies the covariant constraint at EVERY coarse bond (`admissibleWitness_mem_kerQ`), and
  * vanishes on EVERY axial staircase (`admissibleWitness_axialGauge`),

i.e. a nonzero member of `V(Λ̃) = {B : Q₁(U)B = 0, B|_{⋃Ax(y)} = 0}`. Nothing here is an
existential: the witness is a `def`, so there is no free data for a prover to choose (S91).

**The geometric point.** `Λ̃` is nonempty because a block has bonds that escape BOTH exclusions.
Take direction `0` and the base site displaced by `ell-1` in direction `0` and by `1` in direction
`1`. The direction-`0` displacement `ell-1` puts it strictly past the top of every staircase's
direction-`0` leg (whose range is `[y₀, x₀)` with `x₀ < y₀ + ell`), so it lies on no `Γ_{y,x}` — the
same mechanism as `ReparamCDisjoint.droppedBondLast_not_mem_staircase`. The direction-`1`
displacement `1` puts its `1`-coordinate off the coarse sublattice (`≢ 0 mod ell`), so it is not the
dropped bond of any coarse bond either — a dropped bond in direction `0` has all its OTHER
coordinates equal to a coarse site's. Both displacements are needed and each kills one exclusion;
this needs `2 ≤ ell` (at `ell = 1` there is nothing between the two exclusions).

**Relation to `AxialContour.Ax`.** `Ax y ell = ⋃_{x ∈ B(y), x ≠ y} Γ_{y,x}` (`AxialContour.lean`).
The condition proved here quantifies over ALL `x ∈ blockOf y' ell` (not just `x ≠ y'`) and over all
coarse `y'`, so it is at least as strong as vanishing on `⋃_{y'} Ax(y')`; `AxialContour` is not
imported, and `staircasePath` — the object `Ax` is built from — is used directly. -/

/-- **A bond in no staircase and in no dropped set**: direction `0`, based at `y` displaced by
`ell-1` in direction `0` and by `1` in direction `1`. -/
def freeBond (ell : ℕ) (y : PeriodicLatticeSite L) : Bond L :=
  (pathSite (pathSite y 0 (ell - 1)) 1 1, (0 : Fin 3))

theorem freeBond_coord_zero {ell : ℕ} (y : PeriodicLatticeSite L)
    (hfit : (y 0).val + ell ≤ L 0 + 1) (hell2 : 2 ≤ ell) :
    ((freeBond ell y).1 0).val = (y 0).val + (ell - 1) := by
  simp only [freeBond]
  rw [pathSite_apply_ne _ 1 0 1 (by decide), pathSite_apply_self_val]
  exact Nat.mod_eq_of_lt (by omega)

theorem freeBond_coord_one {ell : ℕ} (y : PeriodicLatticeSite L)
    (hfit : (y 1).val + ell ≤ L 1 + 1) (hell2 : 2 ≤ ell) :
    ((freeBond ell y).1 1).val = (y 1).val + 1 := by
  simp only [freeBond]
  rw [pathSite_apply_self_val, pathSite_apply_ne _ 0 1 (ell - 1) (by decide)]
  exact Nat.mod_eq_of_lt (by omega)

theorem freeBond_coord_two {ell : ℕ} (y : PeriodicLatticeSite L) :
    (freeBond ell y).1 2 = y 2 := by
  simp only [freeBond]
  rw [pathSite_apply_ne _ 1 2 1 (by decide), pathSite_apply_ne _ 0 2 (ell - 1) (by decide)]

theorem freeBond_base_mem_block {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L ell) : (freeBond ell y).1 ∈ blockOf y ell := by
  have hfit : ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1 := fun μ =>
    coarse_coord_add_ell_le hdvd μ _ (mem_CoarseLattice.mp hy μ) (y μ).isLt
  rw [mem_blockOf]
  intro ν
  match ν with
  | 0 => rw [freeBond_coord_zero y (hfit 0) hell2]; omega
  | 1 => rw [freeBond_coord_one y (hfit 1) hell2]; omega
  | 2 => rw [freeBond_coord_two y]; omega

/-- **`freeBond` is not the dropped bond of ANY coarse bond.** Its `1`-coordinate is `≢ 0 (mod ell)`,
while a direction-`0` dropped bond has every coordinate other than `0` equal to a coarse site's. -/
theorem freeBond_not_dropped {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L ell) : ¬ IsDropped ell (freeBond ell y) := by
  have hfit1 : (y 1).val + ell ≤ L 1 + 1 :=
    coarse_coord_add_ell_le hdvd 1 _ (mem_CoarseLattice.mp hy 1) (y 1).isLt
  rintro ⟨c, hc⟩
  simp only [droppedBondLast, freeBond, Prod.mk.injEq] at hc
  obtain ⟨hsite, hdir⟩ := hc
  -- the direction is `0`
  have hd : c.2 = (0 : Fin 3) := hdir.symm
  -- coordinate `1` of both sides
  have h1 := congrArg (fun z : PeriodicLatticeSite L => (z 1).val) hsite
  rw [hd, pathSite_apply_ne _ 0 1 (ell - 1) (by decide)] at h1
  have hlhs : ((pathSite (pathSite y 0 (ell - 1)) 1 1) 1).val = (y 1).val + 1 := by
    have := freeBond_coord_one (ell := ell) y hfit1 hell2
    simpa only [freeBond] using this
  rw [hlhs] at h1
  -- `y 1` and `c.1.1 1` are both multiples of `ell`, and they differ by exactly `1`
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy 1)
  have hc1 : (c.1.1 1).val % ell = 0 := mem_CoarseLattice.mp c.1.2 1
  rw [← h1, hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (show 1 < ell by omega)] at hc1
  omega

/-- **`freeBond` lies on NO axial staircase**, for any coarse centre and any block site: its
`0`-coordinate is `y₀ + ell - 1`, at or past the top of every staircase's direction-`0` leg, and the
other two legs have the wrong direction. Same mechanism as
`ReparamCDisjoint.droppedBondLast_not_mem_staircase`, at a different bond. -/
theorem freeBond_not_mem_staircase {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L ell) (y' : PeriodicLatticeSite L)
    (hy' : y' ∈ CoarseLattice L ell) (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y' ell) :
    freeBond ell y ∉ staircasePath y' x := by
  intro he
  have hfit0 : (y 0).val + ell ≤ L 0 + 1 :=
    coarse_coord_add_ell_le hdvd 0 _ (mem_CoarseLattice.mp hy 0) (y 0).isLt
  have hsame : y = y' :=
    AdmissibleSubspace.coarseLattice_unique ell hy hy'
      (freeBond_base_mem_block hell2 hdvd y hy) (staircasePath_base_mem_block hx he)
  subst hsame
  rw [mem_blockOf] at hx
  have hbase : ((freeBond ell y).1 0).val = (y 0).val + (ell - 1) :=
    freeBond_coord_zero y hfit0 hell2
  have key : ∀ (d : Fin 3) (base : PeriodicLatticeSite L),
      freeBond ell y ∈ AdmissibleSubspace.axisSegment base d
        (min (y d).val (x d).val) (max (y d).val (x d).val) → False := by
    intro d base hmem
    obtain ⟨hd, -, -, hhi⟩ := AdmissibleSubspace.mem_axisSegment.mp hmem
    have hd' : (0 : Fin 3) = d := hd
    subst hd'
    have h1 := (hx 0).1
    have h2 := (hx 0).2
    rw [hbase] at hhi
    omega
  simp only [staircasePath, Finset.mem_union] at he
  rcases he with (h2 | h1) | h0
  · exact key 2 _ h2
  · exact key 1 _ h1
  · exact key 0 _ h0

/-- **The named nonzero admissible field.** `fullC` applied to the field supported on the single
free bond. -/
noncomputable def admissibleWitness
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : Bond L → SuTwo :=
  fullC U ell (dinvC U ell) (Pi.single (freeBond ell y) suTwoWitness)

theorem admissibleWitness_at_freeBond {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) :
    admissibleWitness U ell y (freeBond ell y) = suTwoWitness := by
  rw [admissibleWitness, fullC_free U (dinvC U ell) _ (freeBond_not_dropped hell2 hdvd y hy),
    Pi.single_eq_same]

theorem admissibleWitness_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) :
    admissibleWitness U ell y ≠ 0 := by
  intro h0
  have h1 := admissibleWitness_at_freeBond hell2 hdvd U y hy
  rw [h0, Pi.zero_apply] at h1
  exact suTwoWitness_ne_zero h1.symm

theorem admissibleWitness_mem_kerQ {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) :
    ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell (admissibleWitness U ell y) c = 0 :=
  fullC_unconditional_mem_kerQ hell hdvd U _

theorem admissibleWitness_mem_ker {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) :
    admissibleWitness U ell y ∈ LinearMap.ker (lineCoarseRestrictCovLM U ell) :=
  fullC_mem_ker hell hdvd U (dinvC U ell) (dinvC_hinv hell hdvd U) _

theorem admissibleWitness_axialGauge {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) :
    ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, admissibleWitness U ell y e = 0 := by
  refine fullC_unconditional_axialGauge (by omega) hdvd U _ ?_
  intro y' hy' x hx e he
  have hne : e ≠ freeBond ell y := by
    rintro rfl
    exact freeBond_not_mem_staircase hell2 hdvd y hy y' hy' x hx he
  exact Pi.single_eq_of_ne hne _

#print axioms droppedBondLast_injective
#print axioms fullC_free
#print axioms fullC_dropped
#print axioms fullC_add
#print axioms fullC_smul
#print axioms fullC_eq_reparamC_on_reads
#print axioms fullC_mem_kerQ
#print axioms fullC_axialGauge
#print axioms coarseBond_base_not_dropped
#print axioms fullCLM_ne_zero
#print axioms coeffDc_ell2
#print axioms dinvEll2_hinv
#print axioms fullC_ell2_mem_kerQ
#print axioms fullC_ell2_axialGauge
#print axioms fullCLM_ell2_ne_zero
#print axioms fullC_ne_id
#print axioms fullCLM_ne_id
#print axioms pathSite_add
#print axioms gammaPath_pathSite
#print axioms transportPath_hit
#print axioms hit_unique
#print axioms coeffDc_general
#print axioms coeffDc_general_op
#print axioms coeffDc_ell2_op
#print axioms dinvC_hinv
#print axioms coeffDc_ne_zero
#print axioms fullC_unconditional_mem_kerQ
#print axioms fullC_unconditional_axialGauge
#print axioms fullCLM_unconditional_ne_zero
#print axioms coeffDc_ell2_eq_general
#print axioms dinvEll2_eq_dinvC
#print axioms freeBond_not_dropped
#print axioms freeBond_not_mem_staircase
#print axioms freeBond_base_mem_block
#print axioms admissibleWitness_ne_zero
#print axioms admissibleWitness_mem_kerQ
#print axioms admissibleWitness_mem_ker
#print axioms fullC_mem_ker
#print axioms admissibleWitness_axialGauge

end AdalyFormal.Balaban.FullReparamC
