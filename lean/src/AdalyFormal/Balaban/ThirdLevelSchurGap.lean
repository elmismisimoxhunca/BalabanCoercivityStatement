/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ThirdLevelWitness

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ThirdLevelSchurGap.lean` — `[CSTAR-SCHUR-GAP]` ANSWERED, and the level-corrected target STATED

## THE QUESTION (dispatch, task 3)

`[CSTAR-SCHUR-GAP]` (`CStarDeltaKCCoercive` §4) pins the ordering
`deltaJQuadFormCovFaithful ≤ dstarDQuadForm`: the Schur complement never exceeds the raw curl
energy, so a LOWER bound on the raw form (the §3 `C*(D*D)C` coercivity) does NOT transfer down.
**Does the two-level split fix that ordering, or leave it?**

## THE ANSWER, as theorems

**The split LEAVES the ordering and makes it IRRELEVANT.** Three parts, each machine-checked:

1. **The ordering is level-independent** (`schur_le_raw_at_split`, §1): at EVERY `LevelSplit`,
   `deltaKCorr S ≤ dstarDQuadForm` — it is Pythagoras for the orthogonal projection onto
   `D_U(V)`, and moving the fibre level only changes WHICH projection removes energy, never the
   direction of the inequality. No re-typing can reverse it; a downward transfer
   `dstarD → Δ_k` stays impossible.

2. **In the COLLAPSED typing the correct (upward) transfer is identically DEAD** (§2):
   the only lower-bound mechanism the Schur complement admits is duality — pair `D_U B` against
   a witness `u ⊥ D_U(V)` (`CStarLevelCorrected` §3b proves this mechanism is SHARP, so there is
   no other). In the collapsed typing the reparametrized field lies IN `V`, and
   * `collapsed_pairing_dead`: for `B ∈ V`, EVERY admissible `u` pairs to `0` with `D_U B`;
   * `collapsed_factoring_dead`: for `B = fullC B̃` at the SAME level `ℓ`, EVERY §3c factoring
     pair `(u, φ)` has `φ(Q_ℓ(fullC B̃)) = φ(0) = 0`.
   So the numerator of the quantitative duality bound (`deltaJ_ge_dual_pairing_sq`) vanishes
   identically: the transfer route yields exactly `0`, which is the refutation
   `cStarDeltaKC_coercivity_refuted` seen from the transfer side.

3. **At the split the upward transfer FIRES with an explicit constant** (§3):
   `deltaJ_ge_coarse_curl_sq` — for every `ℓ`, every compatible torus, every coarse plaquette
   `P'` and direction `w ≠ 0`, at `U = 1`:

     `ℓ · ⟨w, ∂₁'(Q_ℓ B)(P')⟩² / ⟨w,w⟩ ≤ Δ_k(B)`  (fibre level `ℓ`).

   The lower bound is by the COARSE CURL of `Q_ℓ B` — data at the NEXT level, which the
   `ℓ₁`-level constraint `Q_{ℓ₁} B = 0` does NOT kill when `ℓ < ℓ₁` (witness: `B7`,
   `ThirdLevelWitness`). Instantiated: `third_level_energy_bound` —
   `(1/64) · bondEnergy B7 ≤ deltaKCorr split24 … B7`, an explicit strictly positive coercivity
   constant at the split `(2,4)` on the `ℓ₁`-constraint kernel.

**Summary sentence for the record**: `[CSTAR-SCHUR-GAP]`'s wrong-way ordering is PERMANENT
(Pythagoras, part 1) but was never the obstruction; the real transfer runs UPWARD from the
coarse curl at the fibre level, it is identically zero in the collapsed typing (part 2 — that IS
the level-mismatch refutation), and the two-level split revives it quantitatively (part 3).
What replaces the impossible `dstarD → Δ_k` descent is the CMP96-(2.128)-shaped domination
`Δ_k ≥ c(ℓ) · (coarse curl energy of Q_ℓ B)`, which is exactly the recursion step Bałaban's
`γ₀` argument needs — the coarse curl at level `ℓ` is the input of the NEXT level's Lemma 2.4.

## §4 — the level-corrected coercivity target, stated honestly (open; `def : Prop`, no proof)

`LevelCorrectedCoercivityTargetUniform` — see its docstring for the exact quantifier order and
every disclosed deviation. NOT proved, NOT asserted; the witness instance proved here is the
non-vacuity anchor, not the target.

## Named residuals (OPS-1: earned, with the resistance point stated)

* `[STOKES-COMM-U]` — the general-`U` factoring identity. The exact flat identity CANNOT hold
  covariantly: the transport does not cancel around the `ℓ × ℓ` loop, and
  `CovariantOperators.witness_curvature_ne_zero` exhibits a nonzero curvature defect. The honest
  general-`U` statement is the identity up to `O(α₁ · bondEnergy)` remainder (Bałaban's p.428
  "localizing the operators in `Δ_k`" step). Resistance point, MEASURED (an earlier draft of this
  paragraph guessed "no `RMap`-to-`frobSupBond` bridge lemma exists" — FALSE:
  `RegularUPerturbation.norm_curlDrift_L2_le_sup` IS that bridge, and
  `RegularUQChain.coarseDriftEnergy_le` bounds the `Q`-side drift; with them the perturbed
  pairing `|⟪u, D_U B⟫ − φ(Q₁_{flat} B)| ≤ C·α₁·‖u‖·√(bondEnergy B)` is reachable): the genuine
  stop is one level deeper — the `U ≠ 1` duality criterion needs `u` to APPROXIMATELY annihilate
  `D_U(V_U)` with error measured against `‖D_U v‖`, and converting the reachable
  `O(α₁·√bondEnergy v)` error into `O(α₁·‖D_U v‖)` on the fibre `V_U` is a REVERSE Poincaré on
  the fibre — itself a coercivity statement. That near-circularity, not any missing norm bridge,
  is where the general-`U` transfer resists; Bałaban's own argument breaks it with the U=1 base +
  analyticity in `Mα₀`, which is the (b1)-(b3) program of GOAL_LEMMA §4.
* ~~`[SANDWICH-WITNESS]`~~ **CLOSED 2026-07-27** by `ThirdLevelSandwich.lean` (`fullC_fixes_B7`,
  `sandwich_positivity`, `sandwich_energy_bound`). **This list was STALE and a lane re-derived all
  four declarations before finding them** (LAW-19 duplication, 2026-07-29) — the cost of a residual
  register that outlives its residual. Original text retained: `B7` certifies positivity of `Δ_k` ON the (3.157) constraint kernel
  `ker Q_{ℓ₁}` (the subspace (3.156) is considered on); exhibiting it as `fullC B̃` for the
  per-bond `C` (hence a witness for the `C*Δ_kC` SANDWICH form) needs `fullC (dinvC) B7 = B7`,
  which should hold because `B7` vanishes on every dropped bond and already satisfies the
  constraint (`solvedValue` is then `Dinv c 0 = 0`) — provable from `FullReparamC.fullC_dropped`
  + linearity of `Dinv c`; not done in this pass.
-/

namespace AdalyFormal.Balaban.ThirdLevelSchurGap

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU oneLevelUniv deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit deltaKCorr cStarDeltaKCFormCorr)
open AdalyFormal.Balaban.CStarDeltaKCCoercive (deltaJQuadFormCovFaithful_le_dstarDQuadForm
  lineCoarseRestrictCovLM_fullC)
open AdalyFormal.Balaban.ReparamCSuTwo (coeffDc)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.FullReparamC (fullC)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.ThirdLevelStokes
open AdalyFormal.Balaban.ThirdLevelWitness

variable {L : PeriodicLatticeExtent}

/-! ## §1 — PART 1: the ordering is level-independent; the split does NOT reverse it -/

/-- **`Δ_k ≤ D*D` at EVERY `LevelSplit`.** The Schur complement is the raw curl energy minus the
energy the projection onto `D_U(V(S.fibre))` removes — Pythagoras. Moving the fibre level moves
`V`, never the sign of the removed energy. So the split leaves `[CSTAR-SCHUR-GAP]`'s ordering in
place: a downward transfer of the `C*(D*D)C` lower bound remains impossible, at every level. -/
theorem schur_le_raw_at_split (S : LevelSplit) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    deltaKCorr S levels U B ≤ dstarDQuadForm U B :=
  deltaJQuadFormCovFaithful_le_dstarDQuadForm S.fibre levels U B

#print axioms schur_le_raw_at_split

/-! ## §2 — PART 2: in the collapsed typing, the upward (duality) transfer is identically dead -/

/-- **For `B ∈ V`, EVERY admissible dual witness pairs to zero with `D_U B`.** The quantitative
bound `deltaJ_ge_dual_pairing_sq` has numerator `⟪u, D_U B⟫²` — identically `0` on the collapsed
domain. Since `CStarLevelCorrected` §3b proves duality is SHARP (the only mechanism), the
collapsed transfer yields exactly `0` and nothing else was available: this is the refutation
`cStarDeltaKC_coercivity_refuted`, seen from the transfer side. -/
theorem collapsed_pairing_dead (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (hB : B ∈ gaugeConstraintSubspaceCovFaithful ell levels U)
    (u : PeriodicLatticePlaquette L → SuTwo)
    (hu : ∀ v ∈ gaugeConstraintSubspaceCovFaithful ell levels U,
      covPlaqInner u (curlCovariantLM U v) = 0) :
    covPlaqInner u (curlCovariantLM U B) = 0 :=
  hu B hB

/-- **For the reparametrized field at the SAME level, every §3c factoring pair is dead**:
`φ(Q_ℓ(fullC B̃)) = φ(0) = 0`. The collapse is exactly that `C` lands in the kernel of the very
`Q` the factoring must go through. -/
theorem collapsed_factoring_dead {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo) (φ : (CoarseBond L ell → SuTwo) →ₗ[ℝ] ℝ) :
    φ (lineCoarseRestrictCovLM U ell (fullC U ell Dinv Btil)) = 0 := by
  rw [lineCoarseRestrictCovLM_fullC hell hdvd U Dinv hinv Btil, map_zero]

#print axioms collapsed_pairing_dead
#print axioms collapsed_factoring_dead

/-! ## §3 — PART 3: at the split, the upward transfer fires with explicit constants -/

/-- The window multiplicity, named. -/
noncomputable def windowMult (ell : ℕ) (y : PeriodicLatticeSite L) {μ ν : Fin 3} (hlt : μ < ν)
    (p : PeriodicLatticePlaquette L) : ℕ :=
  ((windowSet ell y).filter (fun t => windowPlaq hlt t = p)).card

theorem stokesU_eq_mult (ell : ℕ) (y : PeriodicLatticeSite L) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) (p : PeriodicLatticePlaquette L) :
    stokesU ell y hlt w p = ((windowMult ell y hlt p : ℝ)) • w := rfl

/-- Each window fibre injects into the `(i,j)` offsets: `mult ≤ ℓ²`. -/
theorem windowMult_le (ell : ℕ) (y : PeriodicLatticeSite L) {μ ν : Fin 3} (hlt : μ < ν)
    (p : PeriodicLatticePlaquette L) :
    windowMult ell y hlt p ≤ ell * ell := by
  classical
  have hcard : ((Finset.range ell) ×ˢ (Finset.range ell)).card = ell * ell := by
    rw [Finset.card_product, Finset.card_range]
  refine le_trans (Finset.card_le_card_of_injOn (fun t => t.2) ?_ ?_) (le_of_eq hcard)
  · intro t ht
    have hts := Finset.mem_filter.mp ht
    have := Finset.mem_product.mp hts.1
    exact this.2
  · intro t ht t' ht' h2
    have hts := Finset.mem_filter.mp ht
    have hts' := Finset.mem_filter.mp ht'
    have hp : windowPlaq hlt t = windowPlaq hlt t' := by rw [hts.2, hts'.2]
    have hfst : pathSite (pathSite t.1 μ t.2.1) ν t.2.2
        = pathSite (pathSite t'.1 μ t'.2.1) ν t'.2.2 := congrArg Prod.fst hp
    have h21 : t.2.1 = t'.2.1 := congrArg Prod.fst h2
    have h22 : t.2.2 = t'.2.2 := congrArg Prod.snd h2
    rw [← h21, ← h22] at hfst
    have hinjν : Function.Injective
        (fun z : PeriodicLatticeSite L => pathSite z ν t.2.2) :=
      Function.Injective.iterate
        (AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_injective ν) t.2.2
    have hinjμ : Function.Injective
        (fun z : PeriodicLatticeSite L => pathSite z μ t.2.1) :=
      Function.Injective.iterate
        (AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_injective μ) t.2.1
    have h1 : t.1 = t'.1 := hinjμ (hinjν hfst)
    exact Prod.ext h1 h2

/-- The multiplicities partition the window: `Σ_p mult p = card windowSet = ℓ⁵` on a compatible
torus with a coarse base point. -/
theorem sum_windowMult (ell : ℕ) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν) :
    ∑ p : PeriodicLatticePlaquette L, windowMult ell y hlt p = ell ^ 5 := by
  classical
  have hpart : (windowSet ell y).card
      = ∑ p : PeriodicLatticePlaquette L, windowMult ell y hlt p :=
    Finset.card_eq_sum_card_fiberwise (fun t _ => Finset.mem_univ (windowPlaq hlt t))
  rw [← hpart]
  unfold windowSet
  rw [Finset.card_product, Finset.card_product, Finset.card_range,
    card_blockOf y ell (coarseLattice_mem_fits hdvd hy)]
  ring

/-- **`⟪u,u⟫ ≤ ℓ⁷ ⟨w,w⟩`** — the norm of the Stokes dual witness, bounded by counting:
`Σ_p mult² ≤ (max mult) · Σ_p mult ≤ ℓ² · ℓ⁵`. -/
theorem stokesU_self_le (ell : ℕ) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) :
    covPlaqInner (stokesU ell y hlt w) (stokesU ell y hlt w)
      ≤ ((ell : ℝ)) ^ 7 * hsInner w w := by
  classical
  unfold covPlaqInner
  have hterm : ∀ p : PeriodicLatticePlaquette L,
      hsInner (stokesU ell y hlt w p) (stokesU ell y hlt w p)
        = ((windowMult ell y hlt p ^ 2 : ℕ) : ℝ) * hsInner w w := by
    intro p
    rw [stokesU_eq_mult, hsInner_smul_left, hsInner_smul_right]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_mul]
  have hn : (∑ p : PeriodicLatticePlaquette L, (windowMult ell y hlt p ^ 2 : ℕ)) ≤ ell ^ 7 := by
    have hstep : (∑ p : PeriodicLatticePlaquette L, windowMult ell y hlt p ^ 2)
        ≤ ∑ p : PeriodicLatticePlaquette L, (ell * ell) * windowMult ell y hlt p := by
      refine Finset.sum_le_sum fun p _ => ?_
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (windowMult_le ell y hlt p)
    refine le_trans hstep ?_
    rw [← Finset.mul_sum, sum_windowMult ell hdvd hy hlt]
    exact Nat.le_of_eq (by ring)
  have hcast : (∑ p : PeriodicLatticePlaquette L,
      ((windowMult ell y hlt p ^ 2 : ℕ) : ℝ)) ≤ ((ell : ℝ)) ^ 7 := by
    rw [← Nat.cast_sum]
    calc ((∑ p : PeriodicLatticePlaquette L, windowMult ell y hlt p ^ 2 : ℕ) : ℝ)
        ≤ ((ell ^ 7 : ℕ) : ℝ) := Nat.cast_le.mpr hn
      _ = ((ell : ℝ)) ^ 7 := by push_cast; ring
  exact mul_le_mul_of_nonneg_right hcast (hsInner_self_nonneg w)

/-- **`0 < ⟪u,u⟫`** for `w ≠ 0` on a live window (`0 < ℓ`): the base tuple `(y,0,0)` gives the
base plaquette multiplicity ≥ 1. -/
theorem stokesU_self_pos (ell : ℕ) (hell : 0 < ell) (y : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hlt : μ < ν) {w : SuTwo} (hw : w ≠ 0) :
    0 < covPlaqInner (stokesU ell y hlt w) (stokesU ell y hlt w) := by
  classical
  have hwpos : 0 < hsInner w w := by
    rcases lt_or_eq_of_le (hsInner_self_nonneg w) with h | h
    · exact h
    · exact absurd (hsInner_self_eq_zero h.symm) hw
  unfold covPlaqInner
  refine Finset.sum_pos' (fun p _ => hsInner_self_nonneg _) ?_
  refine ⟨windowPlaq hlt ((y, 0, 0) : PeriodicLatticeSite L × ℕ × ℕ), Finset.mem_univ _, ?_⟩
  have hyb : y ∈ blockOf y ell := mem_blockOf.mpr (fun ρ => ⟨Nat.le_refl _, by omega⟩)
  have hmem : ((y, 0, 0) : PeriodicLatticeSite L × ℕ × ℕ) ∈ windowSet ell y := by
    unfold windowSet
    rw [Finset.mem_product]
    exact ⟨hyb, Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hell, Finset.mem_range.mpr hell⟩⟩
  have hone : 1 ≤ windowMult ell y hlt (windowPlaq hlt ((y, 0, 0) :
      PeriodicLatticeSite L × ℕ × ℕ)) := by
    refine Finset.card_pos.mpr ⟨((y, 0, 0) : PeriodicLatticeSite L × ℕ × ℕ), ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hmem, rfl⟩
  rw [stokesU_eq_mult, hsInner_smul_left, hsInner_smul_right]
  have h1 : (1 : ℝ) ≤ ((windowMult ell y hlt (windowPlaq hlt ((y, 0, 0) :
      PeriodicLatticeSite L × ℕ × ℕ)) : ℕ) : ℝ) := by exact_mod_cast hone
  have hm : (0 : ℝ) < ((windowMult ell y hlt (windowPlaq hlt ((y, 0, 0) :
      PeriodicLatticeSite L × ℕ × ℕ)) : ℕ) : ℝ) := lt_of_lt_of_le one_pos h1
  exact mul_pos hm (mul_pos hm hwpos)

#print axioms windowMult_le
#print axioms sum_windowMult
#print axioms stokesU_self_le
#print axioms stokesU_self_pos

/-- **THE UPWARD TRANSFER, general in `ℓ` (at `U = 1`).** The Schur complement at fibre level
`ℓ` dominates `ℓ` times each squared coarse-curl component of `Q_ℓ B`, normalized by `⟨w,w⟩`.
This is the CMP96-(2.128)-shaped recursion input: the coarse curl at level `ℓ` is what the next
level's Lemma 2.4 consumes. It is the transfer that REPLACES the impossible downward
`[CSTAR-SCHUR-GAP]` direction. -/
theorem deltaJ_ge_coarse_curl_sq {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    {w : SuTwo} (hw : w ≠ 0) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    (ell : ℝ) * (hsInner w (coarseCurlSuTwo hdvd
        (lineCoarseRestrictCovLM (trivialU L) ell B)
        ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell))) ^ 2 / hsInner w w
      ≤ deltaJQuadFormCovFaithful ell levels (trivialU L) B := by
  have hwpos : 0 < hsInner w w := by
    rcases lt_or_eq_of_le (hsInner_self_nonneg w) with h | h
    · exact h
    · exact absurd (hsInner_self_eq_zero h.symm) hw
  set X : ℝ := hsInner w (coarseCurlSuTwo hdvd
    (lineCoarseRestrictCovLM (trivialU L) ell B)
    ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell)) with hX
  -- the pairing of the Stokes witness with `D_1 B` is `ℓ⁴ X`
  have hpair : covPlaqInner (stokesU ell y hlt w) (curlCovariantLM (trivialU L) B)
      = ((ell : ℝ)) ^ 4 * X := by
    rw [stokes_factoring hell hdvd hy hlt w B, stokesPhi_apply]
  -- the Stokes witness annihilates `D_1(V)`
  have hu : ∀ v ∈ gaugeConstraintSubspaceCovFaithful ell levels (trivialU L),
      covPlaqInner (stokesU ell y hlt w) (curlCovariantLM (trivialU L) v) = 0 := by
    intro v hv
    rw [stokes_factoring hell hdvd hy hlt w v,
      (mem_gaugeConstraintSubspaceCovFaithful.mp hv).1, map_zero]
  have hupos := stokesU_self_pos ell hell y hlt hw
  have h1 := deltaJ_ge_dual_pairing_sq ell levels (trivialU L) B (stokesU ell y hlt w) hu hupos
  rw [hpair] at h1
  refine le_trans ?_ h1
  -- `ℓ X² / ⟨w,w⟩ ≤ (ℓ⁴X)² / ⟪u,u⟫`, via `⟪u,u⟫ ≤ ℓ⁷⟨w,w⟩`
  have hle := stokesU_self_le ell hdvd hy hlt w
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hbig : (0 : ℝ) < ((ell : ℝ)) ^ 7 * hsInner w w := by positivity
  calc (ell : ℝ) * X ^ 2 / hsInner w w
      = (((ell : ℝ)) ^ 4 * X) ^ 2 / (((ell : ℝ)) ^ 7 * hsInner w w) := by
        field_simp
    _ ≤ (((ell : ℝ)) ^ 4 * X) ^ 2
          / covPlaqInner (stokesU ell y hlt w) (stokesU ell y hlt w) := by
        gcongr

#print axioms deltaJ_ge_coarse_curl_sq

/-- **THE EXPLICIT COERCIVITY CONSTANT AT THE SPLIT `(2,4)`** — the quantitative form of
`ThirdLevelWitness.third_level_positivity`: on the `ℓ₁ = 4` constraint-kernel field `B7`,

  `(1/64) · bondEnergy B7 ≤ deltaKCorr split24 … B7`.

Derivation: the transfer theorem gives `2 · ((1/8)⟨w,w⟩)² / ⟨w,w⟩ = ⟨w,w⟩/32`, and
`bondEnergy B7 = 2⟨w,w⟩`. -/
theorem third_level_energy_bound :
    (1 / 64 : ℝ) * bondEnergy B7
      ≤ deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7) B7 := by
  have hwpos := hsInner_witness_pos
  have h := deltaJ_ge_coarse_curl_sq (L := witL7) (by norm_num : 0 < 2) witL7_two_dvd
    y70_coarse2 hlt01 suTwoWitness_ne_zero (oneLevelUniv witL7) B7
  rw [coarseCurl_Q2_B7, hsInner_smul_right] at h
  push_cast at h
  have hgoal : (1 / 64 : ℝ) * bondEnergy B7
      = (2 : ℝ) * ((1 / 8 : ℝ) * hsInner suTwoWitness suTwoWitness) ^ 2
          / hsInner suTwoWitness suTwoWitness := by
    rw [bondEnergy_B7]
    field_simp
    ring
  rw [hgoal]
  exact h

#print axioms third_level_energy_bound

/-! ## §4 — the level-corrected `C*Δ_kC` coercivity target, stated honestly (OPEN) -/

/-- **THE LEVEL-CORRECTED UNIFORM COERCIVITY TARGET** — the honest two-level restatement of
CMP99b p.428's `C*Δ_kC ≥ γ₀ > 0`, replacing the REFUTED collapsed statement
(`cStarDeltaKC_coercivity_refuted`).

Quantifier order (the content): `γ₀` and the regularity threshold `α₀` come FIRST — one constant
for every torus, every split, every level list, every regular background. Then:

* `S : LevelSplit` with `2 ≤ S.fibre` — the fibre is a genuine block (`ℓ₀ = 1` is Bałaban's
  `k = 0` where the Schur mechanism is absent, and `ℓ₀ = 0`/`ℓ = 1` are this tree's known
  degenerate points, §DEGEN);
* both levels compatible with the torus (no `blockOf` truncation), `4 ≤ L μ`;
* `U` REGULAR in the (3.35)–(3.36) proxy sense `frobSupBond U ≤ α₀` (`α₁ = sup_b ‖U_b − 1‖`,
  the tree's standing regularity functional);
* `B̃` supported on the (3.157) free set: axial gauge + vanishing on every dropped bond, both at
  the CONSTRAINT level `S.constr`;
* conclusion: `γ₀ · bondEnergy B̃ ≤ ⟨B̃, C*Δ_kC B̃⟩` with `C` at `S.constr` and `Δ_k`'s fibre at
  `S.fibre` — `cStarDeltaKCFormCorr`, the corrected sandwich.

DISCLOSED deviations from the source (each standing campaign scope, none new here):
`J = 0` (no source term); `levels` abstract with the `R`-clause as-is; the norm is `bondEnergy`
(the campaign's `L²` bond norm — Bałaban's exact normalization is a flagged open check,
GOAL_LEMMA §3); torus proxy for `ℤ³`; `k`-uniformity appears as the SINGLE `(γ₀, α₀)` for all
splits/levels, which is `[UNIF-ALPHA]`'s shape.

`def : Prop` — OPEN, not asserted. The witness theorems above are instances of the
`deltaKCorr`-side positivity, NOT of this target. -/
def LevelCorrectedCoercivityTargetUniform : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (S : LevelSplit), 2 ≤ S.fibre →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      (∀ μ : Fin 3, S.fibre ∣ (L μ + 1)) → (∀ μ : Fin 3, S.constr ∣ (L μ + 1)) →
      ∀ (levels : List (KernelSubspace.Level L))
        (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
          (Dinv : CoarseBond L S.constr → (SuTwo →ₗ[ℝ] SuTwo)),
          (∀ c : CoarseBond L S.constr,
            (coeffDc U S.constr c (droppedBondLast S.constr c)).comp (Dinv c)
              = LinearMap.id) →
          ∀ (Btil : Bond L → SuTwo),
            (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L S.constr →
              ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' S.constr →
              ∀ e ∈ staircasePath y' x, Btil e = 0) →
            (∀ c : CoarseBond L S.constr, Btil (droppedBondLast S.constr c) = 0) →
            γ₀ * bondEnergy Btil ≤ cStarDeltaKCFormCorr S levels U Dinv Btil

#print axioms schur_le_raw_at_split

/-! ## §5 — `[STOKES-COMM-U]`, the NUMERATOR half, closed: general-`U` pairing control

The general-`U` residual splits into (i) controlling the PAIRING `⟪u, D_U B⟫` against its flat
value — closed here with the existing drift machinery — and (ii) the ε-annihilation of `D_U(V_U)`
(the reverse-Poincaré circularity documented in the residual note above), which remains. -/

/-- **The Stokes pairing at a GENERAL background deviates from its flat factored value by at most
`√⟪u,u⟫ · 4√2 · α₁ · √bondEnergy B`** — Cauchy–Schwarz against the curl drift, with the
`k`-independent constant of `RegularUPerturbation.norm_curlDrift_L2_le_sup`. So the numerator of
the (future) perturbed upward transfer is under explicit control for every regular `U`; only the
denominator-side annihilation estimate (ii) is open. -/
theorem general_U_pairing_control {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) :
    |covPlaqInner (stokesU ell y hlt w) (curlCovariantLM U B)
        - stokesPhi ell hdvd hy hlt w (lineCoarseRestrictCovLM (trivialU L) ell B)|
      ≤ Real.sqrt (covPlaqInner (stokesU ell y hlt w) (stokesU ell y hlt w))
          * (4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy B)) := by
  -- replace the flat factored value by the flat pairing
  rw [← stokes_factoring hell hdvd hy hlt w B]
  -- the difference is the pairing against the curl drift
  have hdiff : covPlaqInner (stokesU ell y hlt w) (curlCovariantLM U B)
      - covPlaqInner (stokesU ell y hlt w) (curlCovariantLM (trivialU L) B)
      = covPlaqInner (stokesU ell y hlt w)
          (AdalyFormal.Balaban.RegularUPerturbation.curlDrift U B) := by
    rw [← AdalyFormal.Balaban.CovariantHjMinimizer.covPlaqInner_sub_right]
    rfl
  rw [hdiff]
  -- Cauchy–Schwarz in `PlaqFnL2`
  set u := stokesU ell y hlt w with hu
  set D := AdalyFormal.Balaban.RegularUPerturbation.curlDrift U B with hD
  have hcs : |covPlaqInner u D|
      ≤ Real.sqrt (covPlaqInner u u) * Real.sqrt (covPlaqInner D D) := by
    have h := abs_real_inner_le_norm
      (WithLp.toLp 2 u : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 L) (WithLp.toLp 2 D)
    rw [AdalyFormal.Balaban.CovariantHjMinimizer.inner_plaqFnL2_eq_covPlaqInner] at h
    have hnu : ‖(WithLp.toLp 2 u : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 L)‖
        = Real.sqrt (covPlaqInner u u) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      congr 1
      rw [← real_inner_self_eq_norm_sq,
        AdalyFormal.Balaban.CovariantHjMinimizer.inner_plaqFnL2_eq_covPlaqInner]
    have hnD : ‖(WithLp.toLp 2 D : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 L)‖
        = Real.sqrt (covPlaqInner D D) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      congr 1
      rw [← real_inner_self_eq_norm_sq,
        AdalyFormal.Balaban.CovariantHjMinimizer.inner_plaqFnL2_eq_covPlaqInner]
    rwa [hnu, hnD] at h
  -- `⟪D,D⟫ = plaqEnergy D`, then the drift bound
  have hDD : covPlaqInner D D = AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy D := by
    unfold covPlaqInner AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]
  have hdriftbd := AdalyFormal.Balaban.RegularUPerturbation.norm_curlDrift_L2_le_sup U B
  calc |covPlaqInner u D|
      ≤ Real.sqrt (covPlaqInner u u) * Real.sqrt (covPlaqInner D D) := hcs
    _ = Real.sqrt (covPlaqInner u u)
          * Real.sqrt (AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy D) := by rw [hDD]
    _ ≤ Real.sqrt (covPlaqInner u u)
          * (4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy B)) := by
        exact mul_le_mul_of_nonneg_left hdriftbd (Real.sqrt_nonneg _)

#print axioms general_U_pairing_control

end AdalyFormal.Balaban.ThirdLevelSchurGap
