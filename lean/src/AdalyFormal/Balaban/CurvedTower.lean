/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.TowerMilestone
import AdalyFormal.Balaban.CovariantFibreTransfer
import AdalyFormal.Balaban.WindowStokesGeneralU

-- No `maxRecDepth`/`maxHeartbeats` bump: a strip test (compute/curved_tower/probe_strip.log,
-- EXIT=0, 0 errors) confirms neither is needed, so neither is carried.
set_option autoImplicit false

/-!
# `CurvedTower.lean` — the V-restricted coercivity door AT A CURVED BACKGROUND

Lane record: `compute/curved_tower/PROGRESS.md`.

`TowerMilestone.tower_uniform_coercive` is `k`-uniform, `L`-free and untaxed — and every operator
in it sits at `U = 1` (that module's §2 item 1). This module removes `U = 1` from the ONE-LEVEL
statement: the level operator becomes `Δ_k(U)` at a genuinely curved background, the coarse
gauge-fixing clause becomes the COVARIANT `Q₁(Ū)B = 0`, and the (3.120) correction `Δ′_π` is no
longer taken to be `0` — the `(γ−δ)/q²` recursion is run with a real `δ`.

## §0 — WHAT IS PROVED, AND WHAT IS NOT

Write `α₀ ≥ frobSupBond U` for the FINE background's radius and `ᾱ ≥ frobSupBond Ū` for the COARSE
one, `ε > 0` for the Young parameter of `CovariantFibreTransfer`, and
`γ_c = CovariantFibreTransfer.gammaCurved ᾱ ε`.

1. **`fibre_bound_on_VCurved`** — the coarse fibre bound on the source's subspace read with the
   COVARIANT `Q₁(Ū)`: `γ_c · bondEnergy A ≤ curlEnergy A`. (`CovariantFibreTransfer.transfer_gamma`
   with clause (c2) killing its `P_Ax` term. LAW-19: the aggregate chain is NOT rebuilt.)
2. **`CurvedLevel`** — the curved replacement for `TowerMilestone.Level`. The flat invariant
   `curlEnergy v ≤ ⟨v, Δv⟩` is FALSE at a curved background (that is what
   `ComposedCoercivity.curlEnergy_le_curved` costs `2·⟨v,Δ_k(U)v⟩ + (544α₀+64α₀²)‖v‖²` to repair),
   so the structure carries three parameters:

       hcurl : curlEnergy v ≤ c · (⟨v,Δv⟩ + ⟨v,P_Ax v⟩) + ρ‖v‖²
       hlow  : −σ‖v‖²      ≤ ⟨v,Δv⟩

   `hlow` is NEW and is forced, and every step of `TowerMilestone` that silently used `Level.hpsd`
   needs a replacement. At the lattice level `(c,ρ,σ) = (2, 544α₀+64α₀², 272α₀)`, all three
   theorem-supplied.

   ⚠ **CITATION STRUCK IN PLACE** (2026-08-01, prosecution `compute/curved_prosecution/VERDICT.md`
   attack C, CONVICTED on citation fidelity). This item previously read:
   ~~"`Δ_k(U) = D*_UD_U + Δ′` is NOT positive semidefinite at `U ≠ 1`
   (`DeltaPrimeOperator.deltaPrimeOpNormalized_not_nonneg`)"~~. That theorem is about `Δ′` **alone**,
   not about the composite `Δ_k(U)`; `DeltaPrimeOperator.lean` computes the COMPOSITE's form as
   exactly `0` at the very same witness (`inner_deltaKCLMNormalized_witnessU`) and its own docstring
   says *"no inference about positivity is drawn from a single point, and none is available"*. The
   replacement is a theorem, not a citation: **`deltaK_not_nonneg`** (§4 below) proves the composite
   `Δ_k(U)` fails `0 ≤ ⟨v,Δ_k(U)v⟩` at `centralHolonomyU`, and proves in the SAME statement that this
   `U` is `≠ 1` at the marked bond. Honest scope, also a theorem here:
   `frobSupBond_centralHolonomyU_ge_two` shows that witness has radius `≥ 2`, i.e. it is FAR outside
   the small-`α₀` class this module works in — so whether `Δ_k(U)` is PSD in the small-`α₀` regime is
   NOT established either way in this tree, and does not need to be. `hlow`, proved independently by
   `inner_deltaK_lower` (from `CovariantHj.dstarDQuadForm_nonneg` and
   `DeltaPrimeBound.abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy`), is what the module
   actually needs and has.
3. **`curvedLevel_defect_bound`** — `κ‖v‖² ≤ A_c(⟨v,Δv⟩+⟨v,P v⟩) + 13583253568‖Q₁v‖²` with
   `A_c = 13264896c + 6632448` and `κ = 1 − 13264896ρ − 6632448σ`.
4. **`curvedLevel_fine_pos`** — positive definiteness of (3.128)'s `M = Δ_π + P + aQ*Q` at the
   curved level. ⚠ It needs `a ≥ 13583253568/A_c`: at `U = 1` the flat proof used
   `⟨v,Δv⟩ ≥ 0` to split the three terms, and that is exactly what `hlow` weakens. The `a`-lower
   bound is the honest replacement and it is stated in every consumer.
5. **`curved_gf_on_preimage`** (THE CURVED DOOR) — for every `u` whose FLAT coarse datum lies in
   the curved subspace at the next lattice,

       γ_lvl · ‖u‖² ≤ ⟨u, Δ_k(U) u⟩ + ⟨u, P_Ax u⟩ ,
       γ_lvl = (2γ_c·κ − 13583253568·ρ) / (2γ_c·A_c + 13583253568·c) .

6. **`curved_gf_pi_on_preimage` / `curved_next_coercive_on_VCurved`** (THE CURVED RUNG) — the same
   with (3.120)'s correction present, `(γ_lvl − δ)`, and the RG image `((γ_lvl−δ)/q²)`-coercive on
   the curved subspace at the coarse lattice. This is `TowerOneStep.nextPi_coercive_gf` with a `δ`
   that is NOT zero, and `piCorrectionBound_deltaPrimeNormalized` exhibits a REAL curved `Δ′_π`
   with `δ = 272α₀ > 0`.
7. **Thresholds, two-sided** (§7): `gammaLevel` is positive at `α₀ = ᾱ = 10⁻²⁰` and NONPOSITIVE at
   `α₀ = 10⁻¹⁹` — both proved, at the constants actually consumed.
8. **Flat recovery** (§7): at `(c,ρ,σ) = (1,0,0)` and `ᾱ = 0`, `γ_lvl(ε) = 1/(19897344 +
   (1+ε)·22522555740143616)`, and at `ε = 10⁻¹²` it is within `1 − 10⁻⁹` of `VRestrictedRoute`'s
   own `γ_V = 1/22522555753408512`. The residual `19897344` vs `13264896` is the ONE place this
   module is coarser than the flat door — it merges `master_defect_bound_sharp`'s two coefficients
   because `hlow` no longer lets the `P_Ax` term be dropped for free. Disclosed, not hidden.
9. **Must-fire** (§8): at a genuinely curved fine background AND a genuinely curved coarse
   background (`holonomyElem ≠ 1` at both, kernel-checked), the door fires with BOTH sides strictly
   positive on an explicit nonzero field.

**WHAT IS NOT CLAIMED — read this before consuming anything above.**

* **The rung's averaging operator `Q` is still the FLAT `qCLM (trivialU Λ) 2`.** The obstruction is
  named and is not a matter of taste: `Rung.hQstarInj` needs `Q*` injective, which the tree
  supplies only through `BridgeInverseCarrier.qCLM_surjective_trivialU` — that module's §3 flags it
  as *"the ONLY statement in this module that uses `trivialU`"*. §9 states the missing lemma
  (`qCLM U ell` surjective at general `U`) and the route that would close it, and proves the
  ingredient the route needs is not present in this import closure.
* **No tower at depth.** `TowerMilestone.stepLevel` reproduces `hcurl` with a factor `2` to spare
  BECAUSE the flat invariant has no `‖·‖²` remainder. At `ρ > 0` the step needs `‖u‖²` controlled
  at the level below, i.e. whole-space coercivity, which `OnRangeCoercivity.onRange_false_by_siteConst`
  proves FALSE at the lattice. §10 derives the exact recursion `(c,ρ,σ) ↦ (c',ρ',σ')` that a curved
  step WOULD have to satisfy, and §10a proves — COMPOSED with the step, not as detached arithmetic —
  that `ρ` grows by at least `6791626784 = 13583253568/2` per level (`stepRho_ge_exact`,
  `curvedStepLevel_rho_growth`), with `stepRho_growth_sharp` showing the constant is exact, and
  states the blocked ingredient. **`Ū` at depth is a second, independent gap**: ~~no blocking map `U ↦ Ū` exists
  in this tree~~ (S75 STRUCK 2026-08-01: `BlockedBackground.lean` now pins CMP98 (15)'s blocking at
  SU(2), and its `ubarSU2_constU` chain REFUTES the naive contraction — on constants the blocking is
  the `ell`-th power map and EXPANDS `frobSupBond`, so existence of the map does NOT supply the
  damper this recursion would need). §10's recursion remains stated with `Ū` UNIVERSALLY QUANTIFIED
  at each level and is NOT instantiated. No depth tower is inhabited here.
* `J = 0`; `ell = 2`; `𝔰𝔲(2)`; periodic torus. Standing campaign scope, unchanged.
-/

namespace AdalyFormal.Balaban.CurvedTower

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2 qCLM qstarCLM fineCLM fineCLM_inner)
open AdalyFormal.Balaban.U1AnchorCoarse (coarseExtent)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond
  frobSupBond_nonneg)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAxCLM pAx_nonneg pAxCLM_pos pAxCLM_symm
  inner_pAxCLM_eq' pAx_eq_zero_of_vanishing_on_Ax)
open AdalyFormal.Balaban.AxialContour (Ax)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized deltaKCLMNormalized_symm
  inner_deltaKCLMNormalized_eq deltaPrimeCLMNormalized inner_deltaPrimeCLMNormalized_symm)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.OnRangeCoercivity (norm_sq_eq_bondEnergy injective_of_pos_definite
  next_coercive_gf_on_subspace)
open AdalyFormal.Balaban.ExtentUniformCoercivity (master_defect_bound_sharp coarseEnergy
  norm_sq_qCLM)
open AdalyFormal.Balaban.ComposedCoercivity (driftRemainder driftRemainder_nonneg
  curlEnergy_le_curved)
open AdalyFormal.Balaban.CovariantFibreTransfer (gammaCurved transfer_gamma gammaCurved_pos_iff)
open AdalyFormal.Balaban.VRestrictedRoute (pullS cEnergy bondEnergy_pullS curlEnergy_pullS
  coarseCurlEnergy coarseCurlEnergy_Q_le two_dvd_of_four coarse_two_dvd gammaV gammaV_pos
  vWitFine wSign vWitFine_vanishes_on_Ax vWitFine_Q_zero)
open AdalyFormal.Balaban.TowerMilestone (VLat qLevel qLevelStar qLevel_apply norm_qLevel
  qLevel_hadj qLevelStar_injective coarseIso)
open AdalyFormal.Balaban.TowerOneStep (Rung piOp piOp_apply piOp_symm PiCorrectionBound
  piCorrectionBound_zero gf_pi_of_gf)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le)

variable {L Λ : PeriodicLatticeExtent}

/-! ## §1 — `VCurved`: CMP99b p.428's SUBSPACE WITH A COVARIANT GAUGE-FIXING CLAUSE

`TowerMilestone.VLat Λ` is p.428's three clauses at the lattice `Λ` with clause (c3) read at the
FLAT averaging. The source's `Q₁` is the covariant block average at the background living on that
lattice. `VCurved Λ Ū` is the same three clauses with (c3) at `Ū`; at `Ū = 1` the two predicates
are the SAME statement (`vCurved_trivialU_eq_vLat`, `Iff.rfl`), so nothing is redefined. -/

/-- **THE SOURCE'S SUBSPACE AT `Λ`, WITH THE COVARIANT `Q₁(Ū)`.** -/
def VCurved (Λ : PeriodicLatticeExtent)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (A : Bond Λ → SuTwo) : Prop :=
  True
  ∧ (∀ y ∈ CoarseLattice Λ 2, ∀ b ∈ Ax y 2, A b = 0)
  ∧ (∀ c : CoarseBond Λ 2, lineCoarseRestrictCov Ubar 2 A c = 0)

/-- At the flat background `VCurved` IS `TowerMilestone.VLat`, on the nose. -/
theorem vCurved_trivialU_eq_vLat (A : Bond Λ → SuTwo) :
    VCurved Λ (trivialU Λ) A ↔ VLat Λ A := Iff.rfl

/-- **THE COARSE FIBRE BOUND ON THE CURVED SUBSPACE.** Clause (c2) kills the `P_Ax` term of
`CovariantFibreTransfer.transfer_gamma` and clause (c3) supplies its covariant `Q`-hypothesis, so
`γ_c(ᾱ,ε)·bondEnergy A ≤ curlEnergy A` on `VCurved Λ Ū`. LAW-19: the aggregate chain behind
`transfer_gamma` is reused, not rebuilt. -/
theorem fibre_bound_on_VCurved (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {abar : ℝ} (habar : 0 ≤ abar) (hsup : frobSupBond Ubar ≤ abar)
    {ε : ℝ} (hε : 0 < ε) {A : Bond Λ → SuTwo} (hA : VCurved Λ Ubar A) :
    gammaCurved abar ε * bondEnergy A ≤ curlEnergy A := by
  obtain ⟨-, hc2, hc3⟩ := hA
  have h := transfer_gamma hdvd Ubar habar hsup hε A hc3
  rw [pAx_eq_zero_of_vanishing_on_Ax A _ _ hc2, zero_add] at h
  exact h

/-! ## §2 — `CurvedLevel`: THE INVARIANT THAT SURVIVES CURVATURE

`TowerMilestone.Level` carries `curlEnergy v ≤ ⟨v, Δv⟩`. Two facts make that unavailable at a
curved background, and both are theorems in this tree, not suspicions:

* `ComposedCoercivity.curlEnergy_le_curved` — the flat curl energy is controlled by `Δ_k(U)` only
  up to a factor `2` and an additive `(544α₀ + 64α₀²)·bondEnergy`;
* `deltaK_not_nonneg` (§4 below) — the COMPOSITE `Δ_k(U)` is not positive semidefinite at a curved
  background, so `Level.hpsd` (used silently at four places in `TowerMilestone`) has no curved
  analogue. ⚠ STRUCK IN PLACE: this bullet previously cited
  ~~`DeltaPrimeOperator.deltaPrimeOpNormalized_not_nonneg`~~, a theorem about `Δ′` ALONE — see §0
  item 2 for the full strike and for the scope of the replacement witness.

`CurvedLevel Λ c ρ σ` carries exactly the two facts that replace them. -/

/-- The data a curved level carries. `c` is the operator factor, `ρ` the additive curl remainder,
`σ` the negative part of the operator. At `(c,ρ,σ) = (1,0,0)` this IS `TowerMilestone.Level` plus
the (then automatic) semidefiniteness. -/
structure CurvedLevel (Λ : PeriodicLatticeExtent) (c rho sigma : ℝ) where
  /-- The level's operator. -/
  op : BondFnL2 Λ →L[ℝ] BondFnL2 Λ
  /-- Symmetry. -/
  hsym : ∀ u v : BondFnL2 Λ, (inner ℝ u (op v) : ℝ) = (inner ℝ (op u) v : ℝ)
  /-- **THE CURVED INVARIANT.** -/
  hcurl : ∀ v : BondFnL2 Λ, curlEnergy (WithLp.ofLp v)
    ≤ c * ((inner ℝ v (op v) : ℝ)
        + (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ)) + rho * ‖v‖ ^ 2
  /-- **THE LOWER BOUND.** The curved operator is indefinite; `sigma` bounds how negative. -/
  hlow : ∀ v : BondFnL2 Λ, -(sigma * ‖v‖ ^ 2) ≤ (inner ℝ v (op v) : ℝ)

/-- `A_c = 13264896·c + 6632448`: `master_defect_bound_sharp`'s two coefficients, merged. The merge
is forced by `hlow` — the flat door could drop the `P_Ax` coefficient because `⟨v,Δv⟩ ≥ 0` made
`P_Ax ≤ ⟨v,Δv⟩ + P_Ax` free; at `σ > 0` that costs `6632448·σ‖v‖²`, paid in `defKappa`. -/
noncomputable def defA (c : ℝ) : ℝ := 13264896 * c + 6632448

/-- `κ = 1 − 13264896·ρ − 6632448·σ`: what is left of the defect bound's leading `1`. -/
noncomputable def defKappa (rho sigma : ℝ) : ℝ := 1 - 13264896 * rho - 6632448 * sigma

/-- `13583253568` — `master_defect_bound_sharp`'s coarse-energy coefficient, unchanged. -/
noncomputable def defB : ℝ := 13583253568

theorem defA_pos {c : ℝ} (hc : 0 ≤ c) : 0 < defA c := by
  unfold defA; nlinarith

theorem defB_pos : 0 < defB := by unfold defB; norm_num

/-- **THE CURVED DEFECT BOUND.** `TowerMilestone.level_defect_bound` at a curved level:
`κ‖v‖² ≤ A_c·(⟨v,Δv⟩ + ⟨v,P v⟩) + 13583253568·‖Q₁v‖²`. Every coefficient is composed from
`master_defect_bound_sharp`'s own and the level's `(c,ρ,σ)`; nothing is refitted. -/
theorem curvedLevel_defect_bound {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (v : BondFnL2 Λ) :
    defKappa rho sigma * ‖v‖ ^ 2
      ≤ defA c * ((inner ℝ v (lvl.op v) : ℝ)
          + (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ))
        + defB * ‖qCLM (trivialU Λ) 2 v‖ ^ 2 := by
  have hm := master_defect_bound_sharp hdvd (WithLp.ofLp v)
  have hn : ‖v‖ ^ 2 = bondEnergy (WithLp.ofLp v) := norm_sq_eq_bondEnergy v
  have hP : (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ)
      = pAx (WithLp.ofLp v) (CoarseLattice Λ 2) 2 := inner_pAxCLM_eq' _ _ v
  have hQ : ‖qCLM (trivialU Λ) 2 v‖ ^ 2
      = coarseEnergy (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp v)) := norm_sq_qCLM v
  have hcurl := lvl.hcurl v
  have hlow := lvl.hlow v
  rw [hn] at hcurl hlow
  rw [hP] at hcurl ⊢
  rw [hn, hQ]
  unfold defA defKappa defB
  nlinarith [hm, hcurl, hlow]

/-! ## §3 — POSITIVE DEFINITENESS OF (3.128)'s `M` AT A CURVED LEVEL

`TowerMilestone.level_fine_pos` used `Level.hpsd` to split `⟨v,Mv⟩ ≤ 0` into three vanishing
nonnegative pieces. At `σ > 0` that split is unavailable, and the replacement is a LOWER BOUND ON
`a`: with `a ≥ 13583253568/A_c` the coarse term absorbs the defect bound's own `Q`-coefficient.
Stated with an abstract `Q`/`Q*` (as `level_fine_pos` is) so it serves every codomain. -/

/-- **`M` IS POSITIVE DEFINITE AT A CURVED LEVEL.** The `δ`-slot carries (3.120)'s correction, so
this is the hypothesis a TAXED rung needs, not merely the untaxed one. -/
theorem curvedLevel_fine_pos {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ} {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < defKappa rho sigma)
    {a : ℝ} (ha : defB / defA c ≤ a)
    (Q : BondFnL2 Λ →L[ℝ] K) (Qstar : K →L[ℝ] BondFnL2 Λ)
    (hadj : ∀ (x : BondFnL2 Λ) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hQnorm : ∀ x : BondFnL2 Λ, ‖Q x‖ = ‖qCLM (trivialU Λ) 2 x‖)
    (v : BondFnL2 Λ) (hv : v ≠ 0) :
    (0 : ℝ) < (inner ℝ v
      (fineCLM (piOp lvl.op Dpi) (pAxCLM (CoarseLattice Λ 2) 2) Q Qstar a v) : ℝ) := by
  rw [fineCLM_inner _ _ _ _ _ hadj v, hQnorm v]
  have hAc : 0 < defA c := defA_pos hc
  have haB : defB ≤ defA c * a := by
    rw [div_le_iff₀ hAc] at ha
    linarith [ha]
  set D : ℝ := (inner ℝ v (lvl.op v) : ℝ) with hD
  set P : ℝ := (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ) with hP
  set Z : ℝ := ‖qCLM (trivialU Λ) 2 v‖ ^ 2 with hZ
  have hZnn : (0 : ℝ) ≤ Z := sq_nonneg _
  have hvn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  have hdef : defKappa rho sigma * ‖v‖ ^ 2 ≤ defA c * (D + P) + defB * Z :=
    curvedLevel_defect_bound lvl hdvd v
  have hpiv : (inner ℝ v (Dpi v) : ℝ) ≤ delta * ‖v‖ ^ 2 := le_trans (le_abs_self _) (hpi v)
  by_contra hcon
  simp only [not_lt] at hcon
  have hsplit : (inner ℝ v (piOp lvl.op Dpi v) : ℝ) = D - (inner ℝ v (Dpi v) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [hsplit] at hcon
  -- `D + P ≤ δ‖v‖² − a Z`
  have hDP : D + P ≤ delta * ‖v‖ ^ 2 - a * Z := by nlinarith [hcon, hpiv]
  have hstep : defKappa rho sigma * ‖v‖ ^ 2
      ≤ defA c * (delta * ‖v‖ ^ 2) + (defB - defA c * a) * Z := by
    nlinarith [hdef, hDP, hAc]
  have hneg : (defB - defA c * a) * Z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hZnn
  nlinarith [hstep, hneg, hthr, hvn]

/-! ## §4 — THE LATTICE LEVEL AT A CURVED BACKGROUND

`(c,ρ,σ) = (2, driftRemainder α₀, 272α₀)`. All three are theorem-supplied:
`ComposedCoercivity.curlEnergy_le_curved` gives the first two,
`DeltaPrimeBound.abs_inner_deltaPrimeCLMNormalized_le` together with `CovariantHj.dstarDQuadForm_nonneg`
gives the third. Nothing is chosen. -/

/-- **THE LOWER BOUND ON `Δ_k(U)`.** `⟨v,Δ_k(U)v⟩ ≥ −272α₀‖v‖²`, from `Δ_k = D*D + Δ′` with
`D*D ≥ 0` and `|Δ′| ≤ 272α₀·bondEnergy`. This is the fact `Level.hpsd` had for free at `U = 1`. -/
theorem inner_deltaK_lower {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (v : BondFnL2 L) :
    -(272 * alpha0 * ‖v‖ ^ 2) ≤ (inner ℝ v (deltaKCLMNormalized U v) : ℝ) := by
  obtain ⟨A, rfl⟩ : ∃ A : Bond L → SuTwo, v = WithLp.toLp 2 A := ⟨WithLp.ofLp v, rfl⟩
  have hE : ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 = bondEnergy A := norm_sq_eq_bondEnergy _
  rw [inner_deltaKCLMNormalized_eq, hE]
  have hid : deltaKQuadFormNormalizedCorrected U A
      = AdalyFormal.Balaban.CovariantHj.dstarDQuadForm U A
        + AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported U A := rfl
  have h1 := AdalyFormal.Balaban.CovariantHj.dstarDQuadForm_nonneg U A
  have h2 := abs_le.mp
    (AdalyFormal.Balaban.DeltaPrimeBound.abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy
      halpha U (gaugeRegular_of_frobSupBond_le hsup) A)
  rw [hid]
  linarith [h2.1]

/-- **`Δ_k(U)` IS GENUINELY NOT POSITIVE SEMIDEFINITE — THE COMPOSITE, NOT `Δ′`.** This replaces the
struck citation of `DeltaPrimeOperator.deltaPrimeOpNormalized_not_nonneg` (§0 item 2): that theorem
is about `Δ′` alone, and the composite's form is exactly `0` at that module's witness. Here the
composite operator `deltaKCLMNormalized` itself fails `0 ≤ ⟨v,·v⟩`, at the background
`RegularityHolonomy.centralHolonomyU` (`negOneElem = −1` on one bond, `1` elsewhere). The first
conjunct is the anti-degeneracy clause: the background is genuinely `≠ 1` at the marked bond, so this
is not the flat statement in disguise. LAW-19: the value is
`NormalizedCounterexampleSearch.central_counterexample_neg`
(`deltaKQuadFormNormalizedCorrected centralHolonomyU deltaWitnessConfig = −4`), reused, not rebuilt.

⚠ SCOPE, and it is not a small one — see `frobSupBond_centralHolonomyU_ge_two`: this witness has
radius `≥ 2`, so it lies OUTSIDE the `frobSupBond U ≤ α₀` class every other theorem in this module
works in. It refutes PSD-ness of `Δ_k(·)` as a family; it says nothing about PSD-ness at small `α₀`,
which this tree leaves open in both directions.

Why the old citation was empty, made to fail rather than argued:
`compute/curved_growth/probe_hyp_necessity.lean`'s `struck_citation_witness_is_inert` proves that at
the struck theorem's OWN witness `(witnessU, deltaWitnessConfig)` the composite's form is `≥ 0` — so
that witness supplies no evidence at all for the sentence it used to be attached to. Same operator,
same lattice, only the background changed. -/
theorem deltaK_not_nonneg :
    AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU
        (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 1
      ∧ ¬ (∀ v : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
        (0 : ℝ) ≤ (inner ℝ v (deltaKCLMNormalized
          AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU v) : ℝ)) := by
  refine ⟨AdalyFormal.Balaban.NormalizedCounterexampleSearch.centralHolonomyU_ne_trivial, ?_⟩
  intro h
  have hx := h (WithLp.toLp 2 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig)
  rw [inner_deltaKCLMNormalized_eq] at hx
  exact absurd hx (not_le.mpr
    AdalyFormal.Balaban.NormalizedCounterexampleSearch.central_counterexample_neg)

/-- **THE NOT-PSD WITNESS IS OUTSIDE THIS MODULE'S CLASS, BY A THEOREM.** `‖(−1) − 1‖_F = √8 > 2`, so
`frobSupBond centralHolonomyU ≥ 2`: `deltaK_not_nonneg` is a statement about a background with
`O(1)` radius, never about the `α₀ ≈ 10⁻²⁰` regime §7's thresholds live in. Stated so that no reader
can carry the not-PSD fact into the small-`α₀` regime by accident. -/
theorem frobSupBond_centralHolonomyU_ge_two :
    (2 : ℝ) ≤ frobSupBond AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU := by
  refine le_trans ?_ (AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond
    AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU
    (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)))
  rw [AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU_at_x_mu]
  have hm : ((AdalyFormal.Balaban.DeltaKFull.negOneElem :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = !![(-2 : ℂ), 0; 0, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AdalyFormal.Balaban.DeltaKFull.negOneElem] <;> ring
  have hsq : AdalyFormal.Balaban.RMapLipschitz.frobSq
      (((AdalyFormal.Balaban.DeltaKFull.negOneElem :
        Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 8 := by
    rw [hm]
    simp [AdalyFormal.Balaban.RMapLipschitz.frobSq, Complex.normSq_apply]
    norm_num
  unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm
  rw [hsq]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_nonneg (8:ℝ)]

/-- **THE CURVED LATTICE LEVEL.** `Δ_k(U)`, with the three parameters wired to their theorems. -/
noncomputable def curvedBaseLevel {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) :
    CurvedLevel L 2 (driftRemainder alpha0) (272 * alpha0) where
  op := deltaKCLMNormalized U
  hsym := fun u v => (deltaKCLMNormalized_symm U u v).symm
  hcurl := by
    intro v
    have hE : ‖v‖ ^ 2 = bondEnergy (WithLp.ofLp v) := norm_sq_eq_bondEnergy v
    have hop : (inner ℝ v (deltaKCLMNormalized U v) : ℝ)
        = deltaKQuadFormNormalizedCorrected U (WithLp.ofLp v) :=
      inner_deltaKCLMNormalized_eq U (WithLp.ofLp v)
    have hP : (0 : ℝ) ≤ (inner ℝ v (pAxCLM (CoarseLattice L 2) 2 v) : ℝ) := pAxCLM_pos _ _ v
    have h := curlEnergy_le_curved halpha U hsup (WithLp.ofLp v)
    rw [hop, hE]
    linarith
  hlow := by
    intro v
    have h := inner_deltaK_lower halpha U hsup v
    linarith

@[simp] theorem curvedBaseLevel_op {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) :
    (curvedBaseLevel halpha U hsup).op = deltaKCLMNormalized U := rfl

/-- **THE CURVED `Δ′_π` CHANNEL IS NOT EMPTY.** `Δ′` itself is a (3.120)-shaped correction with
`δ = 272α₀`, strictly positive at every curved background, and symmetric. So the taxed law below is
not a statement about `δ = 0` in disguise. -/
theorem piCorrectionBound_deltaPrimeNormalized {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) :
    PiCorrectionBound (deltaPrimeCLMNormalized U) (272 * alpha0) := by
  intro x
  have h := AdalyFormal.Balaban.DeltaPrimeBound.abs_inner_deltaPrimeCLMNormalized_le
    halpha U (gaugeRegular_of_frobSupBond_le hsup) x
  linarith [h]

theorem deltaPrimeCLMNormalized_sym
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (u v : BondFnL2 L) :
    (inner ℝ u (deltaPrimeCLMNormalized U v) : ℝ)
      = (inner ℝ (deltaPrimeCLMNormalized U u) v : ℝ) :=
  (inner_deltaPrimeCLMNormalized_symm U u v).symm

/-! ## §5 — THE CURVED DOOR: a POSITIVE bound on the source's subspace at a curved background

The three inputs are `curvedLevel_defect_bound` (§2), `fibre_bound_on_VCurved` (§1) and
`VRestrictedRoute.coarseCurlEnergy_Q_le` (Stokes). Stokes is used UNCHANGED and that is not an
oversight: both of its sides are flat objects — the flat `Q₁` and the flat curl energies — so it is
an unconditional identity of this configuration, and the curvature enters through the level's
`(c,ρ,σ)` and through `Ū` at the coarse lattice, not through it. -/

/-- The curved level constant. `γ_lvl = (2γ_c·κ − 13583253568·ρ)/(2γ_c·A_c + 13583253568·c)`,
written with the denominators cleared so no nested division appears. -/
noncomputable def gammaLevel (c rho sigma gc : ℝ) : ℝ :=
  (2 * gc * defKappa rho sigma - defB * rho) / (2 * gc * defA c + defB * c)

theorem gammaLevel_den_pos {c gc : ℝ} (hc : 0 ≤ c) (hgc : 0 < gc) :
    0 < 2 * gc * defA c + defB * c := by
  have h1 : 0 < defA c := defA_pos hc
  have h2 : 0 < defB := defB_pos
  nlinarith

/-- **THE CURVED DOOR AT A LEVEL.** For every `u` whose FLAT coarse datum lies in the source's
subspace at the next lattice read with the COVARIANT `Q₁(Ū)`,

    γ_lvl · ‖u‖² ≤ ⟨u, Δ u⟩ + ⟨u, P_Ax u⟩ .

Every constant is `L`-free and level-free. -/
theorem curved_gf_on_preimage {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsup : frobSupBond Ubar ≤ abar)
    {ε : ℝ} (hε : 0 < ε) (hgc : 0 < gammaCurved abar ε)
    (u : BondFnL2 Λ)
    (hu : VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp (qLevel hdvd u))) :
    gammaLevel c rho sigma (gammaCurved abar ε) * ‖u‖ ^ 2
      ≤ (inner ℝ u (lvl.op u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  set gc : ℝ := gammaCurved abar ε with hgcdef
  -- (a) the fibre bound on the curved subspace, at the coarse lattice
  have hfib := fibre_bound_on_VCurved hdvd' Ubar habar hsup hε hu
  -- (b) the coarse energy IS `‖Q₁ u‖²`
  have hZ : ‖qCLM (trivialU Λ) 2 u‖ ^ 2 = bondEnergy (WithLp.ofLp (qLevel hdvd u)) := by
    rw [← norm_qLevel hdvd u]
    exact norm_sq_eq_bondEnergy _
  -- (c) the coarse curl energy of the pullback is the coarse curl energy of the datum
  have hofLp : WithLp.ofLp (qLevel hdvd u)
      = pullS (by norm_num) hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := rfl
  have hcurlA : curlEnergy (WithLp.ofLp (qLevel hdvd u))
      = coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [hofLp]; exact curlEnergy_pullS _ _ _
  -- (d) Stokes, unchanged
  have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) (by norm_num) hdvd (WithLp.ofLp u)
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hstokes
  rw [hcurlA] at hfib
  rw [← hZ] at hfib
  -- so `gc · Z ≤ (1/2)·curlEnergy u`
  have hZbound : gc * ‖qCLM (trivialU Λ) 2 u‖ ^ 2 ≤ (1 / 2) * curlEnergy (WithLp.ofLp u) := by
    linarith [hfib, hstokes]
  -- (e) the defect bound and the invariant
  have hdef := curvedLevel_defect_bound lvl hdvd u
  have hcurl := lvl.hcurl u
  set D : ℝ := (inner ℝ u (lvl.op u) : ℝ) with hD
  set P : ℝ := (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) with hP
  set Z : ℝ := ‖qCLM (trivialU Λ) 2 u‖ ^ 2 with hZd
  set E : ℝ := ‖u‖ ^ 2 with hEd
  have hZnn : (0 : ℝ) ≤ Z := sq_nonneg _
  have hden : 0 < 2 * gc * defA c + defB * c := gammaLevel_den_pos hc hgc
  have hBpos : (0 : ℝ) < defB := defB_pos
  -- `2 gc Z ≤ curlEnergy u ≤ c(D+P) + ρ E`
  have hkey : 2 * gc * Z ≤ c * (D + P) + rho * E := by linarith [hZbound, hcurl]
  -- combine: `2 gc κ E ≤ 2 gc A_c (D+P) + B (c(D+P) + ρE)`
  have hcomb : 2 * gc * (defKappa rho sigma * E)
      ≤ 2 * gc * (defA c * (D + P)) + defB * (c * (D + P) + rho * E) := by
    nlinarith [hdef, hkey, hgc, hBpos]
  unfold gammaLevel
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hcomb]

/-- **THE TAXED CURVED DOOR.** (3.120)'s correction is present and its two-sided bound `δ` is paid
exactly once: `(γ_lvl − δ)·‖u‖² ≤ ⟨u, Δ_π u⟩ + ⟨u, P_Ax u⟩`. -/
theorem curved_gf_pi_on_preimage {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsup : frobSupBond Ubar ≤ abar)
    {ε : ℝ} (hε : 0 < ε) (hgc : 0 < gammaCurved abar ε)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ} {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (u : BondFnL2 Λ)
    (hu : VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp (qLevel hdvd u))) :
    (gammaLevel c rho sigma (gammaCurved abar ε) - delta) * ‖u‖ ^ 2
      ≤ (inner ℝ u (piOp lvl.op Dpi u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  have hmain := curved_gf_on_preimage lvl hc hdvd hdvd' Ubar habar hsup hε hgc u hu
  have hpiv : (inner ℝ u (Dpi u) : ℝ) ≤ delta * ‖u‖ ^ 2 := le_trans (le_abs_self _) (hpi u)
  have hsplit : (inner ℝ u (piOp lvl.op Dpi u) : ℝ)
      = (inner ℝ u (lvl.op u) : ℝ) - (inner ℝ u (Dpi u) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [hsplit]
  nlinarith [hmain, hpiv]

/-! ## §6 — THE CURVED RUNG, AND THE TAXED ONE-STEP LAW

The rung is `TowerOneStep.Rung` at the index operator `piOp Δ_k(U) Δ′_π` — CMP99b (3.128) fed
`Δ_π`, verbatim, with a `Δ′_π` that is not zero. Its `hinj`/`hMpos` come from §3, i.e. from the
CURVED defect bound, and nowhere from whole-space coercivity.

⚠ **`Q` IS THE FLAT AVERAGING.** See §0's scope note and §9's named lemma. -/

/-- **THE CURVED LEVEL-`Λ` RUNG.** -/
noncomputable def curvedRung {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ}
    (hDpiSym : ∀ u v : BondFnL2 Λ, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < defKappa rho sigma)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : defB / defA c ≤ a) :
    Rung (BondFnL2 Λ) (BondFnL2 (coarseExtent Λ 2)) (piOp lvl.op Dpi) where
  Q := qLevel hdvd
  Qstar := qLevelStar hdvd
  P := pAxCLM (CoarseLattice Λ 2) 2
  a := a
  q := ‖qCLM (trivialU Λ) 2‖
  hadj := qLevel_hadj hdvd
  ha := ha0
  hq := AdalyFormal.Balaban.BridgeInverse.qCLM_norm_pos (by norm_num) hdvd hwide _
  hQ := fun x => by
    rw [norm_qLevel hdvd x]
    exact AdalyFormal.Balaban.BridgeInverse.qCLM_le (trivialU Λ) 2 x
  hDsym := piOp_symm lvl.op Dpi lvl.hsym hDpiSym
  hPsym := pAxCLM_symm (CoarseLattice Λ 2) 2
  hPpos := pAxCLM_pos (CoarseLattice Λ 2) 2
  hinj := injective_of_pos_definite _
    (fun x hx => curvedLevel_fine_pos lvl hc hdvd hpi hthr ha _ _ (qLevel_hadj hdvd)
      (norm_qLevel hdvd) x hx)
  hMpos := fun x hx =>
    curvedLevel_fine_pos lvl hc hdvd hpi hthr ha _ _ (qLevel_hadj hdvd) (norm_qLevel hdvd) x hx
  hQstarInj := qLevelStar_injective hdvd

/-- **THE TAXED CURVED ONE-STEP LAW.** The RG image of the curved level operator is
`((γ_lvl − δ)/q²)`-coercive on the source's curved subspace at the coarse lattice. This is
`TowerOneStep.nextPi_coercive_gf`'s constant with a `δ` that is REAL (§4's
`piCorrectionBound_deltaPrimeNormalized` exhibits one with `δ = 272α₀ > 0`) and a `γ` that is
`gammaLevel` at a curved background. -/
theorem curved_next_coercive_on_VCurved {c rho sigma : ℝ} (lvl : CurvedLevel Λ c rho sigma)
    (hc : 0 ≤ c) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsup : frobSupBond Ubar ≤ abar)
    {ε : ℝ} (hε : 0 < ε) (hgc : 0 < gammaCurved abar ε)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ}
    (hDpiSym : ∀ u v : BondFnL2 Λ, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    {delta : ℝ} (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < defKappa rho sigma)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : defB / defA c ≤ a)
    (hpos : 0 < gammaLevel c rho sigma (gammaCurved abar ε) - delta)
    {B : BondFnL2 (coarseExtent Λ 2)}
    (hB : VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp B)) :
    (gammaLevel c rho sigma (gammaCurved abar ε) - delta)
        / ‖qCLM (trivialU Λ) 2‖ ^ 2 * ‖B‖ ^ 2
      ≤ (inner ℝ B ((curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha).next B) : ℝ) := by
  refine next_coercive_gf_on_subspace
    (curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha) hpos
    (fun C => VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp C)) ?_ hB
  intro C hC
  set r := curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha with hr
  have hQ : qLevel hdvd (r.G (r.Qstar (r.S C))) = C := r.T_S C
  exact curved_gf_pi_on_preimage lvl hc hdvd hdvd' Ubar habar hsup hε hgc hpi
    (r.G (r.Qstar (r.S C))) (by rw [hQ]; exact hC)

/-! ### §6b — THE DOOR AND THE RUNG AT THE LATTICE, WITH EVERY PARAMETER DISCHARGED

§5 and §6 are about an abstract `CurvedLevel`. Here they are read at `Δ_k(U)` itself, with
`(c,ρ,σ) = (2, driftRemainder α₀, 272α₀)` supplied by §4 and with (3.120)'s correction taken to be
`Δ′` — a REAL curved correction, `δ = 272α₀ > 0` at every curved background. -/

/-- The curved door's constant at the lattice: `gammaLevel` at the lattice level's own parameters. -/
noncomputable def gammaVCurved (alpha0 abar eps : ℝ) : ℝ :=
  gammaLevel 2 (driftRemainder alpha0) (272 * alpha0) (gammaCurved abar eps)

/-- **THE CURVED DOOR AT THE LATTICE** — `VRestrictedRoute.coercive_on_VSrc_preimage` at a curved
background. For every fine field whose coarse datum lies in p.428's subspace read with the COVARIANT
`Q₁(Ū)` at the coarse lattice,

    γ_V(α₀,ᾱ,ε) · bondEnergy A ≤ ⟨A, Δ_k(U) A⟩ + P_Ax(A) ,

with `γ_V(α₀,ᾱ,ε)` explicit, `L`-free, positive below the two-sided threshold of §7, and recovering
`VRestrictedRoute.gammaV` to a relative `10⁻⁹` in the flat limit (§7). -/
theorem coercive_on_VSrc_curved (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent L 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    (A : Bond L → SuTwo)
    (hA : VCurved (coarseExtent L 2) Ubar
      (pullS (by norm_num) (two_dvd_of_four hdvd4)
        (lineCoarseRestrictCov (trivialU L) 2 A))) :
    gammaVCurved alpha0 abar eps * bondEnergy A
      ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2 := by
  have hmain := curved_gf_on_preimage (curvedBaseLevel halpha U hsup) (by norm_num)
    (two_dvd_of_four hdvd4) (coarse_two_dvd hdvd4) Ubar habar hsupbar heps hgc
    (WithLp.toLp 2 A) hA
  have hE : ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 = bondEnergy A := norm_sq_eq_bondEnergy _
  have hop : (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
        ((curvedBaseLevel halpha U hsup).op (WithLp.toLp 2 A)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U A := inner_deltaKCLMNormalized_eq U A
  have hP : (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
        (pAxCLM (CoarseLattice L 2) 2 (WithLp.toLp 2 A)) : ℝ)
      = pAx A (CoarseLattice L 2) 2 := inner_pAxCLM_eq' _ _ _
  rw [hE, hop, hP] at hmain
  exact hmain

/-- **THE CURVED RUNG AT THE LATTICE.** Index operator `piOp Δ_k(U) Δ′` — CMP99b (3.128) fed
`Δ_π`, with a correction that is not zero. -/
noncomputable def latticeCurvedRung (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0)
    (hthr : defA 2 * (272 * alpha0) < defKappa (driftRemainder alpha0) (272 * alpha0))
    {a : ℝ} (ha0 : 0 ≤ a) (ha : defB / defA 2 ≤ a) :
    Rung (BondFnL2 L) (BondFnL2 (coarseExtent L 2))
      (piOp (deltaKCLMNormalized U) (deltaPrimeCLMNormalized U)) :=
  curvedRung (curvedBaseLevel halpha U hsup) (by norm_num) (two_dvd_of_four hdvd4)
    (AdalyFormal.Balaban.VRestrictedRoute.coarse_wide hdvd4)
    (deltaPrimeCLMNormalized_sym U) (piCorrectionBound_deltaPrimeNormalized halpha U hsup)
    hthr ha0 ha

/-- **THE CORRECTED OPERATOR IS THE COVARIANT `D*D`.** `Δ_π = Δ_k(U) − Δ′ = D*_U D_U` on the nose.
Recorded so that "the tax channel is real" is a kernel-checked equation and not a claim: the taxed
rung's index operator is a DIFFERENT operator from `Δ_k(U)`, and at `U = 1` the difference vanishes
only because `Δ′` does. -/
theorem latticeCurvedRung_index_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    piOp (deltaKCLMNormalized U) (deltaPrimeCLMNormalized U)
      = AdalyFormal.Balaban.CStarDeltaKCOperator.dstarDCLM U := by
  show deltaKCLMNormalized U - deltaPrimeCLMNormalized U = _
  show AdalyFormal.Balaban.CStarDeltaKCOperator.dstarDCLM U + deltaPrimeCLMNormalized U
      - deltaPrimeCLMNormalized U = _
  abel

/-- **THE TAXED CURVED ONE-STEP LAW AT THE LATTICE.** `((γ_V(α₀,ᾱ,ε) − 272α₀)/q²)`-coercivity of
the RG image on p.428's subspace at the coarse lattice, read with the covariant `Q₁(Ū)`. This is
the `(γ − δ)/q²` recursion the campaign's machinery was built for, with `δ` REAL. -/
theorem next_coercive_on_VSrc_curved (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent L 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    (hthr : defA 2 * (272 * alpha0) < defKappa (driftRemainder alpha0) (272 * alpha0))
    {a : ℝ} (ha0 : 0 ≤ a) (ha : defB / defA 2 ≤ a)
    (hpos : 0 < gammaVCurved alpha0 abar eps - 272 * alpha0)
    {B : BondFnL2 (coarseExtent L 2)}
    (hB : VCurved (coarseExtent L 2) Ubar (WithLp.ofLp B)) :
    (gammaVCurved alpha0 abar eps - 272 * alpha0) / ‖qCLM (trivialU L) 2‖ ^ 2 * ‖B‖ ^ 2
      ≤ (inner ℝ B ((latticeCurvedRung hdvd4 halpha U hsup hthr ha0 ha).next B) : ℝ) :=
  curved_next_coercive_on_VCurved (curvedBaseLevel halpha U hsup) (by norm_num)
    (two_dvd_of_four hdvd4) (AdalyFormal.Balaban.VRestrictedRoute.coarse_wide hdvd4)
    (coarse_two_dvd hdvd4) Ubar habar hsupbar heps hgc (deltaPrimeCLMNormalized_sym U)
    (piCorrectionBound_deltaPrimeNormalized halpha U hsup) hthr ha0 ha hpos hB

/-! ## §7 — THE THRESHOLDS, TWO-SIDED, AND THE FLAT LIMIT -/

/-- `γ_c(0,ε) = 1/((1+ε)·3316224)` — the curved aggregate constant at a flat coarse background. -/
theorem gammaCurved_at_zero (ε : ℝ) : gammaCurved 0 ε = 1 / ((1 + ε) * 3316224) := by
  unfold AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-- **THE FLAT LEVEL CONSTANT, EXACTLY.** At `(c,ρ,σ) = (1,0,0)` and a flat coarse background,
`γ_lvl(ε) = 1/(19897344 + (1+ε)·22522555740143616)`. -/
theorem gammaLevel_flat_eq {ε : ℝ} (hε : 0 < ε) :
    gammaLevel 1 0 0 (gammaCurved 0 ε)
      = 1 / (19897344 + (1 + ε) * 22522555740143616) := by
  rw [gammaCurved_at_zero]
  unfold gammaLevel defKappa defA defB
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  field_simp
  ring

/-- **THE FLAT LIMIT RECOVERS `γ_V`.** At `ε = 10⁻¹²` the curved machinery's constant is within a
relative `10⁻⁹` of `VRestrictedRoute.gammaV = 1/22522555753408512`, the flat door's own constant.
The residual gap is the `19897344` vs `13264896` merge disclosed in §0 item 8 — it is a factor
`1 + 3·10⁻¹⁰`, not a factor `2` and not a factor `48`. -/
theorem gammaLevel_flat_recovers_gammaV :
    gammaV * (1 - 1 / 10 ^ 9) ≤ gammaLevel 1 0 0 (gammaCurved 0 (1 / 10 ^ 12))
      ∧ gammaLevel 1 0 0 (gammaCurved 0 (1 / 10 ^ 12)) ≤ gammaV := by
  rw [gammaLevel_flat_eq (by norm_num : (0:ℝ) < 1 / 10 ^ 12)]
  unfold AdalyFormal.Balaban.VRestrictedRoute.gammaV
  constructor <;> norm_num

/-- **THE THRESHOLD CLOSES.** At `α₀ = ᾱ = 10⁻²⁰`, `ε = 1`, at the LATTICE level's own
`(c,ρ,σ) = (2, driftRemainder α₀, 272α₀)`, the curved level constant is strictly positive. -/
theorem gammaLevel_pos_at_1e_neg_20 :
    0 < gammaLevel 2 (driftRemainder (1 / 10 ^ 20)) (272 * (1 / 10 ^ 20))
      (gammaCurved (1 / 10 ^ 20) 1) := by
  unfold gammaLevel defKappa defA defB AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-- **AND IT FAILS.** At `α₀ = 10⁻¹⁹` — one decade coarser — the SAME constant is nonpositive. So
the threshold is two-sided at the constant actually consumed, not a one-sided decoration. -/
theorem gammaLevel_nonpos_at_1e_neg_19 :
    gammaLevel 2 (driftRemainder (1 / 10 ^ 19)) (272 * (1 / 10 ^ 19))
      (gammaCurved (1 / 10 ^ 20) 1) ≤ 0 := by
  unfold gammaLevel defKappa defA defB AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-- **THE `δ`-THRESHOLD OF §3 IS ALSO TWO-SIDED.** `defA 2 · δ < defKappa ρ σ` holds at the
curved `Δ′` tax `δ = 272α₀` for `α₀ = 10⁻²⁰` and fails at `α₀ = 10⁻⁷`. -/
theorem delta_threshold_two_sided :
    defA 2 * (272 * (1 / 10 ^ 20)) < defKappa (driftRemainder (1 / 10 ^ 20)) (272 * (1 / 10 ^ 20))
      ∧ ¬ (defA 2 * (272 * (1 / 10 ^ 7))
        < defKappa (driftRemainder (1 / 10 ^ 7)) (272 * (1 / 10 ^ 7))) := by
  unfold defA defKappa AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
  constructor <;> norm_num

/-! ## §8 — MUST-FIRE: a GENUINELY CURVED background at both levels, both sides positive

The threshold theorems of §7 say the constant is positive; they say nothing about the statement
being inhabited. This section supplies the inhabitation, at a background whose PLAQUETTE HOLONOMY
is proved `≠ 1` — so it is not the flat case in disguise — on a lattice of side `8`. -/

section MustFire

open AdalyFormal.Balaban.RegularUCurvedWitness (bondU bondU_at bondU_off frobSupBond_bondU
  holonomy_singleBond_base_plaquette)
open AdalyFormal.Balaban.NonFlatBackground (rotElem rotElem_coe rotElem_ne_one frobSq_rotM_sub_one
  sqrt_eight_mul_sq nonflatU_defect_le)
open AdalyFormal.Balaban.BridgeRestricted (rotGen rotGen_ne_zero RMap_rotElem_rotGen)
open AdalyFormal.Balaban.JointInstantiation (lineCoarseRestrictCov_eq_flat_of_line)

/-- **REUSABLE (LAW-19).** `RegularUCurvedWitness.frobSupBond_curvedFamilyU_le` is stated only at
`witL5`; its proof never uses the extent. This is the same statement at an ARBITRARY lattice and an
arbitrary bond, so any lane needing a small curved background at its own extent can use it. -/
theorem frobSupBond_bondRot_le (b0 : Bond L) (t : ℝ) :
    frobSupBond (bondU b0 (rotElem t)) ≤ 2 * Real.sqrt 2 * |t| := by
  rw [frobSupBond_bondU, rotElem_coe, AdalyFormal.Balaban.RMapLipschitz.frobNorm,
    frobSq_rotM_sub_one, ← sqrt_eight_mul_sq]
  exact Real.sqrt_le_sqrt (nonflatU_defect_le t)

/-- Every link of `bondU b₀ (rotElem t)` fixes `rotGen`. -/
theorem bondRot_fix_rotGen (b0 : Bond L) (t : ℝ) (b : Bond L) :
    RMap (bondU b0 (rotElem t) b) rotGen = rotGen := by
  by_cases hb : b = b0
  · rw [hb, bondU_at b0 (rotElem t)]
    exact RMap_rotElem_rotGen t
  · rw [bondU_off b0 (rotElem t) hb, AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rfl

/-- **THE WITNESS IS IN THE CURVED SUBSPACE.** `VRestrictedRoute`'s own nonzero field, at ANY
background whose links fix `rotGen`: clause (c2) is `vWitFine_vanishes_on_Ax`, and clause (c3) holds
COVARIANTLY because `Q₂(Ū)` and `Q₂(1)` agree exactly on a field valued on the line `ℝ·rotGen`
(`JointInstantiation.lineCoarseRestrictCov_eq_flat_of_line`) — no `α`-remainder is used. -/
theorem vWitFine_mem_VCurved (heven : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hfix : ∀ b : Bond Λ, RMap (Ubar b) rotGen = rotGen) :
    VCurved Λ Ubar (vWitFine (Lc := Λ) rotGen) := by
  refine ⟨trivial, fun y hy b hb => vWitFine_vanishes_on_Ax rotGen hy hb, fun cb => ?_⟩
  rw [lineCoarseRestrictCov_eq_flat_of_line Ubar hfix (fun b => wSign b)
    (vWitFine (Lc := Λ) rotGen) (fun _ => rfl) 2 cb]
  exact vWitFine_Q_zero (heven 1) rotGen cb

/-- The witness is NONZERO: it takes the value `rotGen` at an explicit bond. -/
theorem vWitFine_rotGen_ne_zero (hpos : 1 < Λ 0 + 1) :
    vWitFine (Lc := Λ) rotGen ≠ (0 : Bond Λ → SuTwo) :=
  AdalyFormal.Balaban.TowerMilestone.vWitFine_ne_zero hpos rotGen_ne_zero

/-- Side `8` in every direction: `4 ∣ 8` (so both levels are admissible) and `2 ∣ 8`. -/
def cwL : PeriodicLatticeExtent := fun _ => 7

theorem cwL_dvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (cwL μ + 1) := by decide

theorem cwL_dvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (cwL μ + 1) := two_dvd_of_four cwL_dvd4

theorem cwL_coarse_dvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent cwL 2 μ + 1) :=
  coarse_two_dvd cwL_dvd4

theorem cwL_wide : ∀ μ : Fin 3, 2 * 2 ≤ cwL μ + 1 := by decide

/-- The curvature parameter of the must-fire backgrounds, `t = 10⁻²¹`. -/
noncomputable def cwT : ℝ := 1 / 10 ^ 21

theorem cwT_pos : 0 < cwT := by unfold cwT; norm_num

/-- The FINE curved background: `rotElem t` on one bond of `cwL`, `1` elsewhere. -/
noncomputable def cwU : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) cwL :=
  bondU (AdalyFormal.Balaban.FibreCoercivity.zeroSite cwL, (0 : Fin 3)) (rotElem cwT)

/-- The COARSE curved background, on the halved lattice. -/
noncomputable def cwUbar :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent cwL 2) :=
  bondU (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent cwL 2), (0 : Fin 3))
    (rotElem cwT)

theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- Both backgrounds sit inside the `α₀ = 10⁻²⁰` class of §7. `2√2·10⁻²¹ ≤ 4·10⁻²¹ ≤ 10⁻²⁰`. -/
theorem cwU_frobSup : frobSupBond cwU ≤ 1 / 10 ^ 20 := by
  refine le_trans (frobSupBond_bondRot_le _ cwT) ?_
  rw [abs_of_pos cwT_pos]
  unfold cwT
  nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

theorem cwUbar_frobSup : frobSupBond cwUbar ≤ 1 / 10 ^ 20 := by
  refine le_trans (frobSupBond_bondRot_le _ cwT) ?_
  rw [abs_of_pos cwT_pos]
  unfold cwT
  nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

/-- **BOTH BACKGROUNDS ARE GENUINELY CURVED.** The plaquette holonomy at the bond's own base
plaquette is `rotElem t ≠ 1`. So no theorem below is the flat case in disguise. -/
theorem cwU_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem cwU
        (AdalyFormal.Balaban.FibreCoercivity.zeroSite cwL,
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  have h : AdalyFormal.Balaban.DeltaPrime.holonomyElem cwU
      (AdalyFormal.Balaban.FibreCoercivity.zeroSite cwL,
        (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
      = rotElem cwT := by
    unfold cwU
    exact holonomy_singleBond_base_plaquette _ _ _ (rotElem cwT)
      (bondU_at _ _) (fun _ hb => bondU_off _ _ hb) (by decide)
  rw [h]
  exact rotElem_ne_one (ne_of_gt cwT_pos)

theorem cwUbar_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem cwUbar
        (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent cwL 2),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  have h : AdalyFormal.Balaban.DeltaPrime.holonomyElem cwUbar
      (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent cwL 2),
        (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
      = rotElem cwT := by
    unfold cwUbar
    exact holonomy_singleBond_base_plaquette _ _ _ (rotElem cwT)
      (bondU_at _ _) (fun _ hb => bondU_off _ _ hb) (by decide)
  rw [h]
  exact rotElem_ne_one (ne_of_gt cwT_pos)

/-- **MUST-FIRE ON THE COARSE FIBRE BOUND.** At the genuinely curved `Ū` the curved subspace
carries a NONZERO field, the constant is strictly positive there, and both sides of
`fibre_bound_on_VCurved` are strictly positive. -/
theorem fibre_bound_must_fire :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem cwUbar
        (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent cwL 2),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ VCurved (coarseExtent cwL 2) cwUbar (vWitFine (Lc := coarseExtent cwL 2) rotGen)
      ∧ vWitFine (Lc := coarseExtent cwL 2) rotGen ≠ 0
      ∧ 0 < gammaCurved (1 / 10 ^ 20) 1
      ∧ 0 < gammaCurved (1 / 10 ^ 20) 1
          * bondEnergy (vWitFine (Lc := coarseExtent cwL 2) rotGen)
      ∧ gammaCurved (1 / 10 ^ 20) 1
            * bondEnergy (vWitFine (Lc := coarseExtent cwL 2) rotGen)
          ≤ curlEnergy (vWitFine (Lc := coarseExtent cwL 2) rotGen) := by
  have hmem : VCurved (coarseExtent cwL 2) cwUbar (vWitFine (Lc := coarseExtent cwL 2) rotGen) :=
    vWitFine_mem_VCurved cwL_coarse_dvd2 cwUbar (fun b => bondRot_fix_rotGen _ cwT b)
  have hpos1 : 1 < coarseExtent cwL 2 0 + 1 := by decide
  have hne : vWitFine (Lc := coarseExtent cwL 2) rotGen ≠ 0 := vWitFine_rotGen_ne_zero hpos1
  have hgc : 0 < gammaCurved (1 / 10 ^ 20) 1 := by
    rw [gammaCurved_pos_iff]; norm_num
  obtain ⟨b0, hb0⟩ : ∃ b0 : Bond (coarseExtent cwL 2),
      vWitFine (Lc := coarseExtent cwL 2) rotGen b0 ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (funext hcon)
  have hE : 0 < bondEnergy (vWitFine (Lc := coarseExtent cwL 2) rotGen) :=
    AdalyFormal.Balaban.FibreAggregate.bondEnergy_pos _ hb0
  exact ⟨cwUbar_curved, hmem, hne, hgc, mul_pos hgc hE,
    fibre_bound_on_VCurved cwL_coarse_dvd2 cwUbar (by norm_num) cwUbar_frobSup (by norm_num) hmem⟩

/-! ### §8b — MUST-FIRE ON THE DOOR ITSELF

`fibre_bound_must_fire` inhabits §1. This inhabits §6b: an explicit NONZERO fine field on a lattice
of side `8`, at a genuinely curved FINE background AND a genuinely curved COARSE background, at
which `coercive_on_VSrc_curved` fires with both sides strictly positive. -/

/-- The coarse witness of `VRestrictedRoute`, at `cwL`, valued on the line `ℝ·rotGen`. -/
noncomputable def cwF : CoarseBond cwL 2 → SuTwo :=
  AdalyFormal.Balaban.VRestrictedRoute.vWitCoarse cwL_dvd4 rotGen

/-- The fine field carrying it: `FullySupplied.suTwoLift`'s exact section of the flat average. -/
noncomputable def cwA : Bond cwL → SuTwo :=
  AdalyFormal.Balaban.FullySupplied.suTwoLift 2 cwF

theorem cwA_coarse_datum : lineCoarseRestrictCov (trivialU cwL) 2 cwA = cwF :=
  funext (fun c => AdalyFormal.Balaban.ExtentUniformCoercivity.q_suTwoLift cwL_dvd2 cwF c)

theorem cwA_mem : VCurved (coarseExtent cwL 2) cwUbar
    (pullS (by norm_num) (two_dvd_of_four cwL_dvd4)
      (lineCoarseRestrictCov (trivialU cwL) 2 cwA)) := by
  rw [cwA_coarse_datum]
  have h : pullS (by norm_num) (two_dvd_of_four cwL_dvd4) cwF
      = vWitFine (Lc := coarseExtent cwL 2) rotGen :=
    AdalyFormal.Balaban.VRestrictedRoute.pullC_vWitCoarse cwL_dvd4 rotGen
  rw [h]
  exact vWitFine_mem_VCurved cwL_coarse_dvd2 cwUbar (fun b => bondRot_fix_rotGen _ cwT b)

theorem cwA_ne_zero : cwA ≠ 0 := by
  intro h
  have hz : lineCoarseRestrictCov (trivialU cwL) 2 (0 : Bond cwL → SuTwo) = 0 :=
    (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCovLM (trivialU cwL) 2).map_zero
  have hF : cwF = 0 := by rw [← cwA_coarse_datum, h, hz]
  exact AdalyFormal.Balaban.VRestrictedRoute.vWitCoarse_ne_zero cwL_dvd4 rotGen_ne_zero hF

theorem cwA_bondEnergy_pos : 0 < bondEnergy cwA := by
  obtain ⟨b0, hb0⟩ : ∃ b0 : Bond cwL, cwA b0 ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact cwA_ne_zero (funext hcon)
  exact AdalyFormal.Balaban.FibreAggregate.bondEnergy_pos _ hb0

/-- The `δ`-threshold and the coercivity threshold at `α₀ = ᾱ = 10⁻²⁰`, both discharged. -/
theorem cw_thresholds :
    defA 2 * (272 * (1 / 10 ^ 20 : ℝ))
        < defKappa (driftRemainder (1 / 10 ^ 20)) (272 * (1 / 10 ^ 20))
      ∧ 0 < gammaVCurved (1 / 10 ^ 20) (1 / 10 ^ 20) 1 - 272 * (1 / 10 ^ 20 : ℝ) := by
  constructor
  · exact delta_threshold_two_sided.1
  · unfold gammaVCurved gammaLevel defKappa defA defB
      AdalyFormal.Balaban.ComposedCoercivity.driftRemainder
      AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
    norm_num

/-- **MUST-FIRE ON THE CURVED DOOR.** Both backgrounds have plaquette holonomy `≠ 1`; the field is
nonzero; the constant is positive; and the inequality holds with a strictly positive left side —
so the right side, `⟨A, Δ_k(U) A⟩ + P_Ax(A)`, is strictly positive too. -/
theorem door_must_fire :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem cwU
        (AdalyFormal.Balaban.FibreCoercivity.zeroSite cwL,
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem cwUbar
        (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent cwL 2),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ cwA ≠ 0
      ∧ 0 < gammaVCurved (1 / 10 ^ 20) (1 / 10 ^ 20) 1
      ∧ 0 < gammaVCurved (1 / 10 ^ 20) (1 / 10 ^ 20) 1 * bondEnergy cwA
      ∧ 0 < deltaKQuadFormNormalizedCorrected cwU cwA + pAx cwA (CoarseLattice cwL 2) 2
      ∧ gammaVCurved (1 / 10 ^ 20) (1 / 10 ^ 20) 1 * bondEnergy cwA
          ≤ deltaKQuadFormNormalizedCorrected cwU cwA + pAx cwA (CoarseLattice cwL 2) 2 := by
  have hgc : 0 < gammaCurved (1 / 10 ^ 20 : ℝ) 1 := by
    rw [gammaCurved_pos_iff]; norm_num
  have hgam : 0 < gammaVCurved (1 / 10 ^ 20) (1 / 10 ^ 20) 1 := by
    have h := cw_thresholds.2
    have : (0 : ℝ) < 272 * (1 / 10 ^ 20 : ℝ) := by norm_num
    linarith
  have hmain := coercive_on_VSrc_curved cwL_dvd4 (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwU
    cwU_frobSup cwUbar (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) cwUbar_frobSup
    (by norm_num : (0:ℝ) < 1) hgc cwA cwA_mem
  have hE := cwA_bondEnergy_pos
  exact ⟨cwU_curved, cwUbar_curved, cwA_ne_zero, hgam, mul_pos hgam hE,
    lt_of_lt_of_le (mul_pos hgam hE) hmain, hmain⟩

end MustFire

/-! ## §9 — WHAT BLOCKS A COVARIANT `Q` IN THE RUNG, NAMED

`curvedRung`'s `Q` is `qCLM (trivialU Λ) 2`. Replacing it by `qCLM U 2` fails at ONE field of
`TowerOneStep.Rung`, and the failure is mechanical, not conceptual:

* `hadj` — `BridgeInverseCarrier.qCLM_hadj U ell` is general in `U`. ✓
* `hQ`, `hq` — `qCLM_le`, `qCLM_norm_pos` are general in `U`. ✓
* `hinj`, `hMpos` — §3's `curvedLevel_fine_pos` takes `Q` abstractly and only needs
  `‖Qx‖ = ‖qCLM (trivialU Λ) 2 x‖`; at a covariant `Q` that identity is FALSE and would have to be
  replaced by a two-sided comparison. Buildable from
  `WindowStokesGeneralU.norm_lineCoarse_cov_sub_flat_le_block` (constant `8α/ℓ³`).
* **`hQstarInj` — BLOCKED.** `qstar_injective_of_surjective` needs `qCLM U ell` SURJECTIVE, and the
  tree proves surjectivity only at `U = 1` (`BridgeInverseCarrier.qCLM_surjective_trivialU`, whose
  own docstring records it as *"the ONLY statement in this module that uses `trivialU`"*).

**THE MISSING LEMMA, STATED.** `qCLM_surjective_of_small` below is the exact statement that would
unblock it, with the route: `Q₁ ∘ suTwoLift = id` (`ExtentUniformCoercivity.q_suTwoLift`) makes
`suTwoLift` a right inverse of the FLAT `Q`, so `Q_U ∘ suTwoLift = id + (Q_U − Q₁) ∘ suTwoLift`, and
`‖(Q_U − Q₁) ∘ suTwoLift‖ < 1` for small `α` would make it invertible, hence `Q_U` surjective. The
route needs an OPERATOR-NORM bound on `Q_U − Q₁` and an operator-norm bound on `suTwoLift`; the
first is `norm_lineCoarse_cov_sub_flat_le_block` aggregated over coarse bonds, the second is not in
this import closure. **It is named rather than asserted, and nothing above depends on it.** -/

/-- **THE NAMED MISSING PRIMITIVE.** Not proved, not assumed, not used: this is a `Prop`-valued
definition so the statement is in the file as an object rather than as prose (S84). -/
def QCovSurjective (L : PeriodicLatticeExtent) (ell : ℕ) (alpha0 : ℝ) : Prop :=
  ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
    frobSupBond U ≤ alpha0 → Function.Surjective (qCLM U ell)

/-- At `α₀ = 0` the property is INHABITED — by `qCLM_surjective_trivialU`. In fact the coverage is
TOTAL, not just witnessed: `frobSupBond U ≤ 0` forces `U b = 1` at EVERY bond (the Frobenius norm
is nonnegative), so the `α₀ = 0` class collapses to `{trivialU}` and the flat witness IS the whole
class (second-family gate correction, 2026-08-01 — the earlier wording "only in the sense that the
flat witness is in the class" understated this). Stated to show the definition is not vacuous as
written: the flat background satisfies its hypothesis and its conclusion. -/
theorem qCovSurjective_witness {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Surjective (qCLM (trivialU L) ell) :=
  AdalyFormal.Balaban.BridgeInverse.qCLM_surjective_trivialU hell hdvd

/-! ## §9b — §9's NAMED RESIDUAL, CLOSED: `Q_2(U)` IS SURJECTIVE AT SMALL `α`

§9 named `qCLM U ell` surjectivity as the one BLOCKED field of a covariant rung and gave the route.
The route is run here and it closes, with an `L`-FREE threshold. The two ingredients §9 said were
needed both turned out to exist:

* the aggregate operator bound on `Q_2(U) − Q_2(1)` — built below from
  `WindowStokesGeneralU.norm_lineCoarse_cov_sub_flat_le_block` (LAW-19: the per-coarse-bond estimate
  is NOT rebuilt, only summed), plus `CovariantFibreTransfer`'s own block Cauchy–Schwarz;
* the lift's energy bound — `ExtentUniformCoercivity.bondEnergy_suTwoLift_le`, already in the tree
  (`bondEnergy (suTwoLift 2 F) ≤ 32·coarseEnergy F`), which §9 wrongly recorded as absent. That
  sentence of §9 is SUPERSEDED by this section (S75); it is retained there struck.

The threshold is `32α < 1`, i.e. `α < 1/32` — three decades LARGER than any threshold this module's
coercivity constants need, so surjectivity is not what limits the curved door.

⚠ **This does NOT by itself make `curvedRung`'s `Q` covariant.** `curvedLevel_fine_pos` also
consumes `‖Q x‖ = ‖qCLM (trivialU Λ) 2 x‖`, which is FALSE at a covariant `Q`; replacing it needs
the two-sided version of the same estimate fed back through `curvedLevel_defect_bound`. That is the
残り and it is stated in §9's amended list, not here. -/

section QSurjective

open AdalyFormal.Balaban.CovariantFibreTransfer (blockBondSum blockBondSq blockBondSum_nonneg
  blockBondSq_nonneg blockBondSum_sq_le)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf)
open AdalyFormal.Balaban.FibreAggregate (sum_over_blocks sum_shift_site)
open AdalyFormal.Balaban.FullySupplied (suTwoLift suTwoLiftLM)
open AdalyFormal.Balaban.ExtentUniformCoercivity (q_suTwoLift bondEnergy_suTwoLift_le
  norm_sq_coarseFnL2)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.RegularUPerturbation (frobNorm_le_frobSupBond)
open AdalyFormal.Target.ClayStatement (periodicLatticeShift)

/-- **THE PER-COARSE-BOND DRIFT AT `ell = 2`.** `‖(Q_2(U) − Q_2(1))v (b)‖ ≤ α·blockBondSum v`.
The constant is `(1/2⁴)·(2·(4·2)) = 1`, i.e. it is COMPOSED, not chosen: the `1/ℓ⁴` of the (1.18)
normalisation against the `2` of the `RMap` Lipschitz brick and the `4ℓ` path-length bound. -/
theorem qDiff_pointwise
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha)
    (v : Bond Λ → SuTwo) (b : CoarseBond Λ 2) :
    ‖lineCoarseRestrictCov U 2 v b - lineCoarseRestrictCov (trivialU Λ) 2 v b‖
      ≤ alpha * blockBondSum v (b.1 : PeriodicLatticeSite Λ) b.2 := by
  have hal : ∀ e : Bond Λ,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U e : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ alpha :=
    fun e => le_trans (frobNorm_le_frobSupBond U e) hsup
  have h := AdalyFormal.Balaban.WindowStokesGeneralU.norm_lineCoarse_cov_sub_flat_le_block
    U alpha halpha0 hal v b
  have hsum : (∑ x ∈ blockOf (b.1 : PeriodicLatticeSite Λ) 2, ∑ i ∈ Finset.range 2,
        ‖v (pathSite x b.2 i, b.2)‖)
      = blockBondSum v (b.1 : PeriodicLatticeSite Λ) b.2 := by
    unfold blockBondSum
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rfl
  rw [hsum] at h
  refine le_trans h (le_of_eq ?_)
  push_cast
  ring

/-- **THE REMAINDER'S INCIDENCE COUNT OVER COARSE BONDS, EXACT.**
`∑_{c coarse bond} blockBondSq v c = 2·bondEnergy v`. The `2` is the two bonds each block segment
carries, and `sum_shift_site` is what makes it an EQUALITY rather than an estimate.

This is `CovariantFibreTransfer.sum_blockBondSq_eq`'s sum taken over COARSE bonds instead of fine
ones; that module's statement is `= 16·bondEnergy` because each of the `8` sites of a block repeats
the same block sum. Re-derived rather than divided out, because the `8` lives inside its proof. -/
theorem sum_coarse_blockBondSq (v : Bond Λ → SuTwo) :
    (∑ c : CoarseBond Λ 2, blockBondSq v (c.1 : PeriodicLatticeSite Λ) c.2)
      = 2 * bondEnergy v := by
  have hsplit : (∑ c : CoarseBond Λ 2, blockBondSq v (c.1 : PeriodicLatticeSite Λ) c.2)
      = ∑ y ∈ CoarseLattice Λ 2, ∑ mu : Fin 3, blockBondSq v y mu := by
    rw [Fintype.sum_prod_type]
    exact (Finset.sum_subtype (CoarseLattice Λ 2) (fun _ => Iff.rfl)
      (fun y => ∑ mu : Fin 3, blockBondSq v y mu)).symm
  rw [hsplit, Finset.sum_comm]
  have hmu : ∀ mu : Fin 3, (∑ y ∈ CoarseLattice Λ 2, blockBondSq v y mu)
      = 2 * ∑ x : PeriodicLatticeSite Λ, ‖v (x, mu)‖ ^ 2 := by
    intro mu
    have h := sum_over_blocks (L := Λ) (fun x : PeriodicLatticeSite Λ =>
      ‖v (x, mu)‖ ^ 2 + ‖v (periodicLatticeShift x mu, mu)‖ ^ 2)
    have hlhs : (∑ y ∈ CoarseLattice Λ 2, blockBondSq v y mu)
        = ∑ y ∈ CoarseLattice Λ 2, ∑ x ∈ blockOf y 2,
            (‖v (x, mu)‖ ^ 2 + ‖v (periodicLatticeShift x mu, mu)‖ ^ 2) := rfl
    rw [hlhs, h, Finset.sum_add_distrib,
      sum_shift_site mu (fun w : PeriodicLatticeSite Λ => ‖v (w, mu)‖ ^ 2)]
    ring
  rw [Finset.sum_congr rfl (fun mu _ => hmu mu), ← Finset.mul_sum]
  have hbe : bondEnergy v = ∑ mu : Fin 3, ∑ x : PeriodicLatticeSite Λ, ‖v (x, mu)‖ ^ 2 := by
    show (∑ b : Bond Λ, ‖v b‖ ^ 2) = _
    rw [Fintype.sum_prod_type (fun b : Bond Λ => ‖v b‖ ^ 2), Finset.sum_comm]
  rw [hbe]

/-- **THE AGGREGATE DRIFT BOUND.** `coarseEnergy (Q_2(U)v − Q_2(1)v) ≤ 32α²·bondEnergy v`.
`32 = 16·2`: the block Cauchy–Schwarz `16 = 2·|B(y)|` against the exact coarse-bond incidence `2`.
Vanishes QUADRATICALLY as `α → 0`, and is exactly `0` at `U = 1`. -/
theorem coarseEnergy_qDiff_le (hdvd : ∀ mu : Fin 3, (2 : ℕ) ∣ (Λ mu + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha) (v : Bond Λ → SuTwo) :
    coarseEnergy (fun b => lineCoarseRestrictCov U 2 v b
        - lineCoarseRestrictCov (trivialU Λ) 2 v b)
      ≤ 32 * alpha ^ 2 * bondEnergy v := by
  have hterm : ∀ c : CoarseBond Λ 2,
      ‖lineCoarseRestrictCov U 2 v c - lineCoarseRestrictCov (trivialU Λ) 2 v c‖ ^ 2
        ≤ 16 * alpha ^ 2 * blockBondSq v (c.1 : PeriodicLatticeSite Λ) c.2 := by
    intro c
    have h1 := qDiff_pointwise U halpha0 hsup v c
    have h2 := blockBondSum_sq_le hdvd v c.1.2 c.2
    have h0 := blockBondSum_nonneg v (c.1 : PeriodicLatticeSite Λ) c.2
    have hn := norm_nonneg
      (lineCoarseRestrictCov U 2 v c - lineCoarseRestrictCov (trivialU Λ) 2 v c)
    nlinarith [h1, h2, h0, hn, sq_nonneg alpha, mul_nonneg halpha0 h0]
  calc coarseEnergy (fun b => lineCoarseRestrictCov U 2 v b
          - lineCoarseRestrictCov (trivialU Λ) 2 v b)
      ≤ ∑ c : CoarseBond Λ 2, 16 * alpha ^ 2
          * blockBondSq v (c.1 : PeriodicLatticeSite Λ) c.2 :=
        Finset.sum_le_sum (fun c _ => hterm c)
    _ = 16 * alpha ^ 2 * (2 * bondEnergy v) := by
        rw [← Finset.mul_sum, sum_coarse_blockBondSq]
    _ = 32 * alpha ^ 2 * bondEnergy v := by ring

/-- The exact section of the FLAT average, promoted to the `ℓ²` carriers. -/
noncomputable def liftLM (Λ : PeriodicLatticeExtent) : CoarseFnL2 Λ 2 →ₗ[ℝ] BondFnL2 Λ :=
  ((WithLp.linearEquiv 2 ℝ (Bond Λ → SuTwo)).symm.toLinearMap).comp
    (((suTwoLiftLM Λ 2 : (CoarseBond Λ 2 → SuTwo) →ₗ[ℝ] (Bond Λ → SuTwo))).comp
      (WithLp.linearEquiv 2 ℝ (CoarseBond Λ 2 → SuTwo)).toLinearMap)

theorem liftLM_ofLp (F : CoarseFnL2 Λ 2) :
    WithLp.ofLp (liftLM Λ F) = suTwoLift 2 (WithLp.ofLp F) := rfl

/-- `Q_2(1) ∘ lift = id`, on the carriers. -/
theorem qCLM_liftLM (hdvd : ∀ mu : Fin 3, (2 : ℕ) ∣ (Λ mu + 1)) (F : CoarseFnL2 Λ 2) :
    qCLM (trivialU Λ) 2 (liftLM Λ F) = F := by
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond Λ 2 → SuTwo)).injective ?_
  funext b
  exact q_suTwoLift hdvd (WithLp.ofLp F) b

/-- `‖lift F‖² ≤ 32‖F‖²` — `bondEnergy_suTwoLift_le` on the carriers. -/
theorem norm_sq_liftLM_le (F : CoarseFnL2 Λ 2) : ‖liftLM Λ F‖ ^ 2 ≤ 32 * ‖F‖ ^ 2 := by
  have h1 : ‖liftLM Λ F‖ ^ 2 = bondEnergy (suTwoLift 2 (WithLp.ofLp F)) := by
    rw [norm_sq_eq_bondEnergy, liftLM_ofLp]
  have h2 : ‖F‖ ^ 2 = coarseEnergy (WithLp.ofLp F) := norm_sq_coarseFnL2 (WithLp.ofLp F)
  rw [h1, h2]
  exact bondEnergy_suTwoLift_le (WithLp.ofLp F)

/-- **§9's RESIDUAL, CLOSED.** `Q_2(U)` is surjective at every background with `frobSupBond U ≤ α`
and `32α < 1`, on every compatible torus. `L`-free, and at `α = 0` it degrades to
`BridgeInverseCarrier.qCLM_surjective_trivialU` — which is NOT invoked in the proof, so this is an
independent route to the flat statement as well. -/
theorem qCLM_surjective_of_small (hdvd : ∀ mu : Fin 3, (2 : ℕ) ∣ (Λ mu + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (hsup : frobSupBond U ≤ alpha) (hsmall : 32 * alpha < 1) :
    Function.Surjective (qCLM U 2) := by
  set T : CoarseFnL2 Λ 2 →ₗ[ℝ] CoarseFnL2 Λ 2 := ((qCLM U 2).toLinearMap).comp (liftLM Λ) with hT
  have hTapp : ∀ F : CoarseFnL2 Λ 2, T F = qCLM U 2 (liftLM Λ F) := fun _ => rfl
  have hkey : ∀ F : CoarseFnL2 Λ 2, ‖T F - F‖ ^ 2 ≤ 1024 * alpha ^ 2 * ‖F‖ ^ 2 := by
    intro F
    set v : Bond Λ → SuTwo := suTwoLift 2 (WithLp.ofLp F) with hv
    have hflat : ∀ b : CoarseBond Λ 2,
        WithLp.ofLp F b = lineCoarseRestrictCov (trivialU Λ) 2 v b :=
      fun b => (q_suTwoLift hdvd (WithLp.ofLp F) b).symm
    have hfun : WithLp.ofLp (T F - F)
        = fun b => lineCoarseRestrictCov U 2 v b - lineCoarseRestrictCov (trivialU Λ) 2 v b := by
      funext b
      show WithLp.ofLp (T F) b - WithLp.ofLp F b = _
      rw [hflat b]
      rfl
    have hn : ‖T F - F‖ ^ 2 = coarseEnergy (WithLp.ofLp (T F - F)) :=
      norm_sq_coarseFnL2 (WithLp.ofLp (T F - F))
    rw [hn, hfun]
    have hagg := coarseEnergy_qDiff_le hdvd U halpha0 hsup v
    have hlift : bondEnergy v ≤ 32 * ‖F‖ ^ 2 := by
      have h := norm_sq_liftLM_le (Λ := Λ) F
      rw [norm_sq_eq_bondEnergy, liftLM_ofLp] at h
      exact h
    nlinarith [hagg, hlift, sq_nonneg alpha, norm_nonneg F]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 (fun F hF => ?_)
    have h0 : T F = 0 := hF
    have h1 := hkey F
    rw [h0, zero_sub, norm_neg] at h1
    have h2 : (0 : ℝ) ≤ ‖F‖ ^ 2 := sq_nonneg _
    have h3 : (1 : ℝ) - 1024 * alpha ^ 2 > 0 := by nlinarith [halpha0, hsmall]
    have h4 : ‖F‖ ^ 2 ≤ 0 := by nlinarith [h1, h3]
    have h5 : ‖F‖ = 0 := by nlinarith [h4, norm_nonneg F]
    exact norm_eq_zero.1 h5
  have hsurjT : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  intro G
  obtain ⟨F, hF⟩ := hsurjT G
  exact ⟨liftLM Λ F, by rw [← hTapp F]; exact hF⟩

/-- **AND THE THRESHOLD IS NOT DECORATIVE.** `32α < 1` closes at `α = 1/33` and fails at
`α = 1/32`, so the smallness hypothesis is stated at the value it is actually used at. -/
theorem qSurj_threshold_two_sided :
    32 * (1 / 33 : ℝ) < 1 ∧ ¬ (32 * (1 / 32 : ℝ) < 1) := by
  constructor <;> norm_num

end QSurjective

/-! ## §10 — WHY THERE IS NO CURVED TOWER AT DEPTH HERE, DERIVED

`TowerMilestone.stepLevel` reproduces `hcurl` with a factor `2` to spare. The derivation of the
CURVED step, run to the point where it breaks:

    curl_{k+1}(B) ≤ ½·curl_k(u)                                    (Stokes, `ell = 2`)
                 ≤ ½·(c·(⟨u,Δ_k u⟩+⟨u,P_k u⟩) + ρ‖u‖²)             (`hcurl` at level `k`)
                 = ½·c·⟨B,Δ_{k+1}B⟩ + ½·ρ‖u‖²                      (the lift identity)

so the step closes iff `‖u‖²` — the norm of the HARMONIC LIFT, not of `B` — is controlled. The
curved defect bound gives `κ‖u‖² ≤ A_c⟨B,Δ_{k+1}B⟩ + 13583253568‖B‖²`, so it IS controlled, and the
recursion is

    m  = κ − A_c·δ
    c' = c/2 + (cδ+ρ)·A_c/(2m) ,   ρ' = (cδ+ρ)·13583253568/(2m) ,
    σ' = (σ+δ)·13583253568/(m + (σ+δ)·A_c) .

These are `stepC`, `stepRho`, `stepSigma` VERBATIM — read the definitions below and compare term by
term. ⚠ CORRECTED IN PLACE (2026-08-01): this display previously read
~~`c' = c/2 + ρ·A_c/(2κ) , ρ' = ρ·13583253568/(2κ) , σ' = σ·13583253568/(κ + σ·A_c)`~~, which is the
`δ = 0` SPECIALIZATION of the three definitions, printed without saying so — it silently dropped the
`(3.120)` correction `δ` that the whole point of §6 is to carry. No theorem depended on the display;
the defect was prose-vs-definition drift of exactly the kind attack A convicted, found while
repairing that attack, and it is fixed rather than noted.

§10a below records the one number that matters, AS A COMPOSED THEOREM: `stepRho_ge_exact` derives
`stepRho c ρ σ δ ≥ 6791626784·ρ` from the step's OWN hypotheses, and `curvedStepLevel_rho_growth`
states it with `curvedStepLevel` itself inside the statement. `stepRho_growth_sharp` proves the
constant cannot be raised, so `6791626784 = 13583253568/2` is derived, not rounded. That is a REAL
threshold, not an obstruction — but it is not `k`-uniform, and `k`-uniformity is what CMP99b p.428
asserts.

⚠ STRUCK IN PLACE (2026-08-01, prosecution `compute/curved_prosecution/VERDICT.md` attack A). This
paragraph previously read: ~~"`step_rho_growth` below records the one number that matters: `ρ` is
multiplied by `13583253568/(2κ) ≈ 6.79·10⁹` at every level, so a depth-`k` curved tower needs
`α₀ ≲ 10⁻²⁰·(1.5·10⁻¹⁰)^k`."~~ Two defects, both now repaired or struck. (i) `step_rho_growth` did
NOT record that: it was arithmetic about an unconstrained `κ`, applied to `stepRho` nowhere in the
kernel; the composition is now written down (§10a). (ii) The depth-`k` extrapolation
`α₀ ≲ 10⁻²⁰·(1.5·10⁻¹⁰)^k` is not proved anywhere in this tree and is STRUCK, not softened: it needs
a `k`-fold iteration of the step, whose hypotheses (`hthr` at every level, and a coarse background
`Ū` at every level) are exactly what the next paragraph says do not exist here. What is certified is
the ONE-LEVEL multiplier; nothing about a depth-`k` admissible `α₀` is claimed.

**The step is NOT built here, and the reason is not the arithmetic above.** It is `Ū`: the level
`k+1` statement needs the coarse background at level `k+1`, i.e. the BLOCKED background `Ū` of
CMP98 pp.29–30 (the `(3.19)` composite). No map `U ↦ Ū` exists in this tree, so §5's `Ū` is a free
universally quantified datum, and a depth-`k` chain would need `k` of them with their radii tied to
`α₀` by a blocking estimate that is not available. Fabricating that tie would be exactly the
`S91`/free-data defect the registry exists to catch. -/

section Step

variable {c rho sigma delta : ℝ}

/-- `c' = c/2 + (cδ+ρ)·A_c/(2m)`, `m = κ − A_c·δ`. -/
noncomputable def stepC (c rho sigma delta : ℝ) : ℝ :=
  c / 2 + (c * delta + rho) * defA c / (2 * (defKappa rho sigma - defA c * delta))

/-- `ρ' = (cδ+ρ)·13583253568/(2m)`. THIS is the number that forbids `k`-uniformity. -/
noncomputable def stepRho (c rho sigma delta : ℝ) : ℝ :=
  (c * delta + rho) * defB / (2 * (defKappa rho sigma - defA c * delta))

/-- `σ' = (σ+δ)·13583253568/(m + (σ+δ)A_c)`. -/
noncomputable def stepSigma (c rho sigma delta : ℝ) : ℝ :=
  (sigma + delta) * defB / ((defKappa rho sigma - defA c * delta) + (sigma + delta) * defA c)

/-- **THE THREE FACTS ABOUT THE HARMONIC LIFT** a curved step needs: the lift identity with the
`(3.120)` correction split off, the curved defect bound read at the lift, and Stokes. Stated at an
ARBITRARY rung tied to the level's own `Q`/`P`, so it is reusable (LAW-19). -/
theorem step_lift_facts (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ} (hpi : PiCorrectionBound Dpi delta)
    (r : Rung (BondFnL2 Λ) (BondFnL2 (coarseExtent Λ 2)) (piOp lvl.op Dpi))
    (hQeq : ∀ x : BondFnL2 Λ, r.Q x = qLevel hdvd x)
    (hPeq : r.P = pAxCLM (CoarseLattice Λ 2) 2)
    (B : BondFnL2 (coarseExtent Λ 2)) :
    ((inner ℝ (r.G (r.Qstar (r.S B))) (lvl.op (r.G (r.Qstar (r.S B)))) : ℝ)
        + (inner ℝ (r.G (r.Qstar (r.S B)))
            (pAxCLM (CoarseLattice Λ 2) 2 (r.G (r.Qstar (r.S B)))) : ℝ)
        ≤ (inner ℝ B (r.next B) : ℝ) + delta * ‖r.G (r.Qstar (r.S B))‖ ^ 2)
      ∧ ((defKappa rho sigma - defA c * delta) * ‖r.G (r.Qstar (r.S B))‖ ^ 2
        ≤ defA c * (inner ℝ B (r.next B) : ℝ) + defB * ‖B‖ ^ 2)
      ∧ curlEnergy (WithLp.ofLp B)
        ≤ 1 / 2 * curlEnergy (WithLp.ofLp (r.G (r.Qstar (r.S B)))) := by
  set u : BondFnL2 Λ := r.G (r.Qstar (r.S B)) with hu
  have hQu : r.Q u = B := r.T_S B
  have hQlev : qLevel hdvd u = B := by rw [← hQeq u]; exact hQu
  have hnorm : ‖qCLM (trivialU Λ) 2 u‖ = ‖B‖ := by
    rw [← norm_qLevel hdvd u, hQlev]
  have hAc : (0 : ℝ) ≤ defA c := (defA_pos hc).le
  -- (i) the lift identity, with the correction split off
  have hlift := AdalyFormal.Balaban.TowerMilestone.rung_inner_next_lift r B
  rw [hPeq] at hlift
  have hsplit : (inner ℝ u (piOp lvl.op Dpi u) : ℝ)
      = (inner ℝ u (lvl.op u) : ℝ) - (inner ℝ u (Dpi u) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [hsplit] at hlift
  have hpiv : (inner ℝ u (Dpi u) : ℝ) ≤ delta * ‖u‖ ^ 2 := le_trans (le_abs_self _) (hpi u)
  have hone : (inner ℝ u (lvl.op u) : ℝ)
      + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ)
      ≤ (inner ℝ B (r.next B) : ℝ) + delta * ‖u‖ ^ 2 := by linarith [hlift, hpiv]
  -- (ii) the curved defect bound at the lift
  have hdef := curvedLevel_defect_bound lvl hdvd u
  rw [hnorm] at hdef
  have hmul : defA c * ((inner ℝ u (lvl.op u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ))
      ≤ defA c * ((inner ℝ B (r.next B) : ℝ) + delta * ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hone hAc
  have he1 : defA c * ((inner ℝ B (r.next B) : ℝ) + delta * ‖u‖ ^ 2)
      = defA c * (inner ℝ B (r.next B) : ℝ) + defA c * (delta * ‖u‖ ^ 2) := by ring
  have he2 : (defKappa rho sigma - defA c * delta) * ‖u‖ ^ 2
      = defKappa rho sigma * ‖u‖ ^ 2 - defA c * (delta * ‖u‖ ^ 2) := by ring
  have htwo : (defKappa rho sigma - defA c * delta) * ‖u‖ ^ 2
      ≤ defA c * (inner ℝ B (r.next B) : ℝ) + defB * ‖B‖ ^ 2 := by
    rw [he2]; rw [he1] at hmul; linarith [hdef, hmul]
  -- (iii) Stokes
  have hofLp : WithLp.ofLp B
      = pullS (by norm_num) hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [← hQlev]; rfl
  have hcurlB : curlEnergy (WithLp.ofLp B)
      = coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [hofLp]; exact curlEnergy_pullS _ _ _
  have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) (by norm_num) hdvd (WithLp.ofLp u)
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hstokes
  refine ⟨hone, htwo, ?_⟩
  rw [hcurlB]
  linarith [hstokes]

/-- **THE CURVED STEP.** The curved invariant DOES propagate to the RG image: the level-`(k+1)`
operator, on the halved lattice's own bond carrier, is a `CurvedLevel` with parameters
`(c',ρ',σ') = (stepC, stepRho, stepSigma)`. So the OPERATOR side of a curved tower is not blocked.

Note what this is NOT: it is not `k`-uniform. `TowerMilestone.stepLevel` reproduced its invariant
with a factor `2` TO SPARE; here `ρ` is multiplied by at least `6791626784 = 13583253568/2` at every
level. That degradation is real and is stated rather than averaged away.

⚠ CITATION CORRECTED IN PLACE (2026-08-01, prosecution attack A): this note previously cited
~~`step_rho_growth`~~ for the multiplier, which is arithmetic about an unconstrained `κ` and was
applied to `stepRho` nowhere. The correct citations are `stepRho_ge_exact` (the composition, from
this definition's own hypotheses) and `curvedStepLevel_rho_growth` (the same with THIS definition in
the statement); `stepRho_growth_sharp` shows the constant is the exact infimum. The clause
~~"so the admissible `α₀` shrinks by that factor per level of depth"~~ is also struck: no `k`-fold
iteration of this step exists in this tree (see §10 on `Ū`), so no statement about depth-`k`
admissible `α₀` is certified here. -/
noncomputable def curvedStepLevel (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ}
    (hDpiSym : ∀ u v : BondFnL2 Λ, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hdelta : 0 ≤ delta) (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < defKappa rho sigma)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : defB / defA c ≤ a) :
    CurvedLevel (coarseExtent Λ 2) (stepC c rho sigma delta) (stepRho c rho sigma delta)
      (stepSigma c rho sigma delta) where
  op := (curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha).next
  hsym := fun u v =>
    AdalyFormal.Balaban.TowerMilestone.rung_next_sym
      (curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha) u v
  hcurl := by
    intro B
    obtain ⟨hone, htwo, hthree⟩ :=
      step_lift_facts lvl hc hdvd hpi (curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha)
        (fun _ => rfl) rfl B
    set r := curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha with hr
    set u : BondFnL2 Λ := r.G (r.Qstar (r.S B)) with hu
    set X : ℝ := (inner ℝ B (r.next B) : ℝ) with hX
    have hmpos : 0 < defKappa rho sigma - defA c * delta := by linarith [hthr]
    have hAc : 0 < defA c := defA_pos hc
    have hBpos : (0 : ℝ) < defB := defB_pos
    have hcoef : (0 : ℝ) ≤ c * delta + rho := by nlinarith
    have hlv := lvl.hcurl u
    have hu2 : ‖u‖ ^ 2
        ≤ (defA c * X + defB * ‖B‖ ^ 2) / (defKappa rho sigma - defA c * delta) := by
      rw [le_div_iff₀ hmpos]; linarith [htwo]
    have hmulc : c * ((inner ℝ u (lvl.op u) : ℝ)
          + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ))
        ≤ c * (X + delta * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hone hc
    have hstep : curlEnergy (WithLp.ofLp B)
        ≤ c / 2 * X + (c * delta + rho) / 2 * ‖u‖ ^ 2 := by
      have hexp : c * (X + delta * ‖u‖ ^ 2) = c * X + c * delta * ‖u‖ ^ 2 := by ring
      rw [hexp] at hmulc
      linarith [hthree, hlv, hmulc]
    have hcnn : (0 : ℝ) ≤ stepC c rho sigma delta := by
      unfold stepC
      have h1 : (0 : ℝ)
          ≤ (c * delta + rho) * defA c / (2 * (defKappa rho sigma - defA c * delta)) :=
        div_nonneg (mul_nonneg hcoef hAc.le) (by linarith)
      linarith [h1, hc]
    have hmul2 : (c * delta + rho) / 2 * ‖u‖ ^ 2
        ≤ (c * delta + rho) / 2
          * ((defA c * X + defB * ‖B‖ ^ 2) / (defKappa rho sigma - defA c * delta)) :=
      mul_le_mul_of_nonneg_left hu2 (by linarith)
    have hid : (c * delta + rho) / 2
          * ((defA c * X + defB * ‖B‖ ^ 2) / (defKappa rho sigma - defA c * delta))
        = stepC c rho sigma delta * X - c / 2 * X
          + stepRho c rho sigma delta * ‖B‖ ^ 2 := by
      unfold stepC stepRho
      field_simp
      ring
    rw [hid] at hmul2
    have hPB : (0 : ℝ)
        ≤ (inner ℝ B (pAxCLM (CoarseLattice (coarseExtent Λ 2) 2) 2 B) : ℝ) :=
      pAxCLM_pos _ _ B
    have hmono : stepC c rho sigma delta * X
        ≤ stepC c rho sigma delta
          * (X + (inner ℝ B (pAxCLM (CoarseLattice (coarseExtent Λ 2) 2) 2 B) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hcnn
    linarith [hstep, hmul2, hmono]
  hlow := by
    intro B
    obtain ⟨hone, htwo, -⟩ :=
      step_lift_facts lvl hc hdvd hpi (curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha)
        (fun _ => rfl) rfl B
    set r := curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha with hr
    set u : BondFnL2 Λ := r.G (r.Qstar (r.S B)) with hu
    set X : ℝ := (inner ℝ B (r.next B) : ℝ) with hX
    have hmpos : 0 < defKappa rho sigma - defA c * delta := by linarith [hthr]
    have hAc : 0 < defA c := defA_pos hc
    have hBpos : (0 : ℝ) < defB := defB_pos
    have hsd : (0 : ℝ) ≤ sigma + delta := by linarith
    have hlow := lvl.hlow u
    have hPu : (0 : ℝ) ≤ (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := pAxCLM_pos _ _ u
    have hXlow : -((sigma + delta) * ‖u‖ ^ 2) ≤ X := by nlinarith [hone, hlow, hPu]
    have hden : 0 < (defKappa rho sigma - defA c * delta) + (sigma + delta) * defA c := by
      nlinarith
    have hscale : (sigma + delta) * ((defKappa rho sigma - defA c * delta) * ‖u‖ ^ 2)
        ≤ (sigma + delta) * (defA c * X + defB * ‖B‖ ^ 2) :=
      mul_le_mul_of_nonneg_left htwo hsd
    have hXm : -X * (defKappa rho sigma - defA c * delta)
        ≤ (sigma + delta) * ‖u‖ ^ 2 * (defKappa rho sigma - defA c * delta) :=
      mul_le_mul_of_nonneg_right (by linarith [hXlow]) hmpos.le
    unfold stepSigma
    rw [neg_le, div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [hscale, hXm]

end Step

/-! ### §10a — THE `ρ`-GROWTH FACTOR, AND ITS COMPOSITION WITH THE STEP

The prosecution (`compute/curved_prosecution/VERDICT.md`, attack A) CONVICTED the earlier state of
this section: `step_rho_growth` was free-standing arithmetic about an unconstrained `kappa`, applied
to `stepRho` nowhere in the kernel, so the flagship quantitative claim lived only in prose. It is now
composed. Seven declarations are added; THREE carry the claim, four are their supports
(`step_m_le_one`, `stepRho_ge_6e9`, `stepRho_pure_rho`, `stepRho_growth_sharp`):

* `defB_div_ge` — the arithmetic core, at the EXACT constant `defB/2 = 6791626784` (derived: `defB`
  is even, so `defB/2` is an integer; `13583253568 = 2·6791626784`). `step_rho_growth` is now a
  corollary of it and is no longer the load-bearing statement.
* `stepRho_ge_exact` — **the composition**: from `curvedStepLevel`'s OWN hypotheses (a subset of
  them: `hc`, `hrho`, `hsigma`, `hdelta`, `hthr`), `6791626784·ρ ≤ stepRho c ρ σ δ`.
* `curvedStepLevel_rho_growth` — the same, with the STEP ITSELF in the statement: the RG image level
  exists at the stepped parameters, its operator IS `(curvedRung …).next` (so the existential cannot
  be met by some other, easier level), and its `ρ`-index obeys the bound.

`stepRho_growth_sharp` proves `6791626784` cannot be raised, so the constant is derived rather than
rounded down: for every `K > 6791626784` there is an admissible `(c,ρ,0,0)` with `stepRho < K·ρ`.

Hypothesis necessity (OPS-3, made to fail rather than argued): `compute/curved_growth/
probe_hyp_necessity.lean` proves, for each of `stepRho_ge_exact`'s FIVE hypotheses separately, that
deleting THAT one and keeping the other four makes the conclusion FALSE at an explicit rational
witness — `needs_hc` `(-1,0,0,1)`, `needs_hrho` `(0,−10⁻¹²,10⁻⁷,0)`, `needs_hsigma` `(0,10⁻⁹,−1,0)`,
`needs_hdelta` `(1,10⁻⁹,0,−1)`, `needs_hthr` `(0,10⁻⁶,0,0)`. 5 of 5 fire; the all-hypotheses control
in the same file does not. Note `needs_hrho`'s witness needs `σ > 0` as well: at `σ = δ = 0` a
negative `ρ` does NOT break the bound, so the obvious counterexample is not one. -/

/-- **THE EXACT `ρ`-MULTIPLIER LOWER BOUND.** `defB/(2κ) ≥ defB/2 = 6791626784` for every
`κ ∈ (0,1]`. The extreme case is `κ = 1`, where the inequality is an EQUALITY (`defB = 13583253568`
is even), which is why the constant is exact rather than rounded; every `κ < 1` only makes the left
side larger. -/
theorem defB_div_ge {kappa : ℝ} (hk : kappa ≤ 1) (hk0 : 0 < kappa) :
    (6791626784 : ℝ) ≤ defB / (2 * kappa) := by
  unfold defB
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * kappa)]
  nlinarith

/-- **THE `ρ`-GROWTH FACTOR, COMPUTED.** At `κ` near `1` the curved step multiplies the curl
remainder by more than `6.7·10⁹`. Now a rounded corollary of `defB_div_ge`; the statement is
unchanged. ⚠ STRUCK: this docstring used to add ~~"Kernel-visible, so §10's prose cannot drift from
it"~~ — the prose drifted anyway, because this statement never mentioned `stepRho`. Kernel-visibility
of a DETACHED fact prevents nothing; only `stepRho_ge_exact` does. -/
theorem step_rho_growth {kappa : ℝ} (hk : kappa ≤ 1) (hk0 : 0 < kappa) :
    (6.7 : ℝ) * 10 ^ 9 ≤ defB / (2 * kappa) :=
  le_trans (by norm_num) (defB_div_ge hk hk0)

section StepGrowth

variable {c rho sigma delta : ℝ}

/-- `m = κ − A_c·δ ≤ 1` under the step's own sign hypotheses: `κ ≤ 1` because `ρ, σ ≥ 0`, and
`A_c·δ ≥ 0` because `c, δ ≥ 0`. All four sign hypotheses are consumed HERE; `hrho` is consumed a
SECOND time inside `stepRho_ge_exact`, where the bound is multiplied through by `cδ + ρ ≥ ρ ≥ 0`.
Each of the five hypotheses is load-bearing, with an explicit counterexample per hypothesis in
`compute/curved_growth/probe_hyp_necessity.lean`. -/
theorem step_m_le_one (hc : 0 ≤ c) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hdelta : 0 ≤ delta) :
    defKappa rho sigma - defA c * delta ≤ 1 := by
  have hAd : (0 : ℝ) ≤ defA c * delta := mul_nonneg (defA_pos hc).le hdelta
  unfold defKappa
  linarith

/-- **THE COMPOSITION, AT THE EXACT CONSTANT.** From `curvedStepLevel`'s own hypotheses, the curved
step's output curl-remainder obeys `stepRho c ρ σ δ ≥ 6791626784·ρ`. The chain is: `m ≤ 1`
(`step_m_le_one`) ⟹ `defB/(2m) ≥ 6791626784` (`defB_div_ge`) ⟹ multiply by `cδ + ρ ≥ ρ ≥ 0`. -/
theorem stepRho_ge_exact (hc : 0 ≤ c) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hdelta : 0 ≤ delta)
    (hthr : defA c * delta < defKappa rho sigma) :
    (6791626784 : ℝ) * rho ≤ stepRho c rho sigma delta := by
  have hcd : (0 : ℝ) ≤ c * delta := mul_nonneg hc hdelta
  have hmpos : 0 < defKappa rho sigma - defA c * delta := by linarith
  have hmle : defKappa rho sigma - defA c * delta ≤ 1 := step_m_le_one hc hrho hsigma hdelta
  have hkey := defB_div_ge hmle hmpos
  have hstep : stepRho c rho sigma delta
      = (c * delta + rho) * (defB / (2 * (defKappa rho sigma - defA c * delta))) := by
    unfold stepRho; ring
  rw [hstep]
  have hpos : (0 : ℝ) < defB / (2 * (defKappa rho sigma - defA c * delta)) :=
    div_pos defB_pos (by linarith)
  nlinarith [hkey, hrho, hcd, hpos]

/-- The rounded form of `stepRho_ge_exact`, i.e. the number §0/§10 quote. -/
theorem stepRho_ge_6e9 (hc : 0 ≤ c) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hdelta : 0 ≤ delta)
    (hthr : defA c * delta < defKappa rho sigma) :
    (6.7 : ℝ) * 10 ^ 9 * rho ≤ stepRho c rho sigma delta := by
  have h := stepRho_ge_exact hc hrho hsigma hdelta hthr
  have hnum : (6.7 : ℝ) * 10 ^ 9 = 6700000000 := by norm_num
  rw [hnum]
  nlinarith [h, hrho]

/-- `stepRho` on the `δ = σ = 0` slice, in closed form. Note it does NOT depend on `c` there: `c`
enters `stepRho` only through `c·δ` and `A_c·δ`. Used by `stepRho_growth_sharp`. -/
theorem stepRho_pure_rho (c r : ℝ) :
    stepRho c r 0 0 = r * defB / (2 * (1 - 13264896 * r)) := by
  unfold stepRho defA defKappa; ring

/-- **THE CONSTANT `6791626784` IS EXACT, NOT ROUNDED DOWN.** For every `K` strictly above it there
is an admissible instance — `σ = δ = 0`, `ρ = r > 0`, `A_c·δ = 0 < κ`, at ANY `c` — where the growth
factor is strictly below `K`. So `stepRho_ge_exact` cannot be improved by raising its constant, and
the number is a derived infimum rather than a padded guess. (The infimum is approached as `ρ ↓ 0` and
is not attained: at `ρ > 0` the factor is strictly larger, which only makes the obstruction worse.)

S91 note: the conclusion is existential and the existential datum `r` IS the content — this is a
counterexample statement, so a witness is what it must produce. `K` and `c` are universally
quantified and the operator/constant slots are all pinned to this module's own definitions. -/
theorem stepRho_growth_sharp (c : ℝ) {K : ℝ} (hK : (6791626784 : ℝ) < K) :
    ∃ r : ℝ, 0 < r ∧ defA c * 0 < defKappa r 0 ∧ stepRho c r 0 0 < K * r := by
  have hK0 : (0 : ℝ) < K := by linarith
  set b : ℝ := 6791626784 / K with hbdef
  have hb0 : 0 < b := div_pos (by norm_num) hK0
  have hb1 : b < 1 := by rw [hbdef, div_lt_one hK0]; linarith
  have hKb : K * b = 6791626784 := by rw [hbdef]; field_simp
  refine ⟨(1 - b) / (2 * 13264896), div_pos (by linarith) (by norm_num), ?_, ?_⟩
  · unfold defA defKappa
    have hh : (13264896 : ℝ) * ((1 - b) / (2 * 13264896)) = (1 - b) / 2 := by ring
    rw [hh]; linarith
  · set r : ℝ := (1 - b) / (2 * 13264896) with hrdef
    have hr : 0 < r := div_pos (by linarith) (by norm_num)
    rw [stepRho_pure_rho c r]
    have hden : (2 : ℝ) * (1 - 13264896 * r) = 1 + b := by rw [hrdef]; ring
    rw [hden, div_lt_iff₀ (by linarith : (0:ℝ) < 1 + b)]
    unfold defB
    nlinarith [mul_pos hr (sub_pos.mpr hK), hKb, hr]

/-- **THE COMPOSITION WITH THE STEP ITSELF IN THE STATEMENT.** Under exactly `curvedStepLevel`'s
hypotheses: the RG image IS a `CurvedLevel` at `(stepC, stepRho, stepSigma)`, its operator is the
rung's own `next` (so the existential is not satisfiable by an easier, unrelated level), and its
`ρ`-index is at least `6791626784·ρ` — equivalently at least `6.7·10⁹·ρ`. This is the theorem the
flagship claim "`ρ` is multiplied by `≥ 6.7·10⁹` per level" now cites; before the repair the claim
was assembled only in prose out of `curvedStepLevel` and the free-standing `step_rho_growth`.

S91 note: the existential is over `CurvedLevel …` at parameters that are DEFINED, not free, and the
first conjunct pins the witness's operator, so there is no free data in the conclusion. -/
theorem curvedStepLevel_rho_growth (lvl : CurvedLevel Λ c rho sigma) (hc : 0 ≤ c)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    {Dpi : BondFnL2 Λ →L[ℝ] BondFnL2 Λ}
    (hDpiSym : ∀ u v : BondFnL2 Λ, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hdelta : 0 ≤ delta) (hpi : PiCorrectionBound Dpi delta)
    (hthr : defA c * delta < defKappa rho sigma)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : defB / defA c ≤ a) :
    ∃ lvl' : CurvedLevel (coarseExtent Λ 2) (stepC c rho sigma delta)
        (stepRho c rho sigma delta) (stepSigma c rho sigma delta),
      lvl'.op = (curvedRung lvl hc hdvd hwide hDpiSym hpi hthr ha0 ha).next
        ∧ (6791626784 : ℝ) * rho ≤ stepRho c rho sigma delta
        ∧ (6.7 : ℝ) * 10 ^ 9 * rho ≤ stepRho c rho sigma delta :=
  ⟨curvedStepLevel lvl hc hrho hsigma hdvd hwide hDpiSym hdelta hpi hthr ha0 ha, rfl,
    stepRho_ge_exact hc hrho hsigma hdelta hthr, stepRho_ge_6e9 hc hrho hsigma hdelta hthr⟩

end StepGrowth

/-! ## §11 — AXIOM AUDIT -/

#print axioms VCurved
#print axioms vCurved_trivialU_eq_vLat
#print axioms fibre_bound_on_VCurved
#print axioms CurvedLevel
#print axioms defA
#print axioms defKappa
#print axioms defB
#print axioms defA_pos
#print axioms defB_pos
#print axioms curvedLevel_defect_bound
#print axioms curvedLevel_fine_pos
#print axioms inner_deltaK_lower
#print axioms deltaK_not_nonneg
#print axioms frobSupBond_centralHolonomyU_ge_two
#print axioms curvedBaseLevel
#print axioms curvedBaseLevel_op
#print axioms piCorrectionBound_deltaPrimeNormalized
#print axioms deltaPrimeCLMNormalized_sym
#print axioms gammaLevel
#print axioms gammaLevel_den_pos
#print axioms curved_gf_on_preimage
#print axioms curved_gf_pi_on_preimage
#print axioms curvedRung
#print axioms curved_next_coercive_on_VCurved
#print axioms gammaCurved_at_zero
#print axioms gammaLevel_flat_eq
#print axioms gammaLevel_flat_recovers_gammaV
#print axioms gammaLevel_pos_at_1e_neg_20
#print axioms gammaLevel_nonpos_at_1e_neg_19
#print axioms delta_threshold_two_sided
#print axioms frobSupBond_bondRot_le
#print axioms bondRot_fix_rotGen
#print axioms vWitFine_mem_VCurved
#print axioms vWitFine_rotGen_ne_zero
#print axioms cwL
#print axioms cwL_dvd4
#print axioms cwL_dvd2
#print axioms cwL_coarse_dvd2
#print axioms cwL_wide
#print axioms cwT
#print axioms cwT_pos
#print axioms cwU
#print axioms cwUbar
#print axioms sqrt_two_le_two
#print axioms cwU_frobSup
#print axioms cwUbar_frobSup
#print axioms cwU_curved
#print axioms cwUbar_curved
#print axioms fibre_bound_must_fire
#print axioms QCovSurjective
#print axioms qCovSurjective_witness
#print axioms gammaVCurved
#print axioms coercive_on_VSrc_curved
#print axioms latticeCurvedRung
#print axioms latticeCurvedRung_index_eq
#print axioms next_coercive_on_VSrc_curved
#print axioms cwF
#print axioms cwA
#print axioms cwA_coarse_datum
#print axioms cwA_mem
#print axioms cwA_ne_zero
#print axioms cwA_bondEnergy_pos
#print axioms cw_thresholds
#print axioms door_must_fire
#print axioms qDiff_pointwise
#print axioms sum_coarse_blockBondSq
#print axioms coarseEnergy_qDiff_le
#print axioms liftLM
#print axioms liftLM_ofLp
#print axioms qCLM_liftLM
#print axioms norm_sq_liftLM_le
#print axioms qCLM_surjective_of_small
#print axioms qSurj_threshold_two_sided
#print axioms stepC
#print axioms stepRho
#print axioms stepSigma
#print axioms step_lift_facts
#print axioms curvedStepLevel
#print axioms defB_div_ge
#print axioms step_rho_growth
#print axioms step_m_le_one
#print axioms stepRho_ge_exact
#print axioms stepRho_ge_6e9
#print axioms stepRho_pure_rho
#print axioms stepRho_growth_sharp
#print axioms curvedStepLevel_rho_growth

end AdalyFormal.Balaban.CurvedTower
