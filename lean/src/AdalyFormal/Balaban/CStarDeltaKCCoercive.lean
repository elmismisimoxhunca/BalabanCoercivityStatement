/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FullReparamC
import AdalyFormal.Balaban.RegularUDomainWitness
import AdalyFormal.Balaban.CStarDeltaKCCompose

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `CStarDeltaKCCoercive.lean` — the `C*(D_U^*D_U)C` coercivity on the free (3.157) coordinates,
and the PRECISE reason it is NOT `C*Δ_kC` in the encoding as it stands.

## What is PROVED here (§3, the headline)

For every background `U`, every compatible torus (`4 ≤ L μ`, `2 ∣ L μ + 1`), block side `ell = 2`,
every per-coarse-bond right inverse `Dinv` of `coeffDc` at the corrected dropped bond, and every
free field `B̃` that

* satisfies the su(2) **axial gauge** (`B̃ b = 0` on every staircase `Γ_{y,x}`), and
* **vanishes on every dropped bond** `droppedBondLast 2 c` (i.e. `B̃` is genuinely supported on the
  (3.157) free set `Λ̃ = Λ \ (⋃ Ax(y) ∪ ⋃ B(c)∩c)`),

and under the two `α₁`-smallness hypotheses `hthr`/`hsmall` of
`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` (`α₁ = frobSupBond U`; Bałaban's
`Mα₀` small, (3.35)–(3.36)):

  `γ'' · bondEnergy B̃  ≤  cStarDstarDCForm a 2 U Dinv B̃`,
  `γ'' = (√(γ₀ − 64α₁²) − 4√2·α₁)²`,  `γ₀ = (1/108)(1/2⁴)`,

for EVERY `a : ℝ` — the mass term is proved to vanish identically on `image (fullC)`
(`cStarDstarDCForm_eq_dstarD`), so the constant is `a`-free.

`cStarDstarDCForm a ell U Dinv B̃ := ⟨C B̃, D_U^*D_U (C B̃)⟩ − a⟨Q₁(C B̃), Q₁(C B̃)⟩` with
`C = fullC U ell Dinv` the FULL (3.157) reparametrization and `D_U^*D_U` the CMP99b (3.10) leading
term `‖D_U ·‖²` (`CovariantHj.dstarDQuadForm`). So the headline is the `C*(·)C` sandwich over the
**leading `D*D` term**, in the free coordinates `B̃`, with an EXPLICIT `k`-independent constant.

## ⚠ HONEST SCOPE — what this is NOT (read before quoting the headline)

**(a) LEADING TERM ONLY.** The object bounded below is `dstarDQuadForm U (C B̃) = ‖D_U(C B̃)‖²`,
the (3.10)/(3.156) `D*D` term, NOT the campaign's encoded `Δ_k`
(`DeltaKSuTwoAssembly.deltaKSuTwoForm`, whose leading term is the Schur complement
`CovariantHjFaithful.deltaJQuadFormCovFaithful`). §4 proves, in the kernel, that the two are ordered
the WRONG way for a transfer: `deltaJQuadFormCovFaithful ≤ dstarDQuadForm`
(`deltaJQuadFormCovFaithful_le_dstarDQuadForm`). A lower bound on the larger object is NOT a lower
bound on the smaller one. This is a genuine mathematical gap, named `[CSTAR-SCHUR-GAP]`, NOT
plumbing. The `J ≠ 0` source term `−2⟨H₁D̃⁽²⁾(B),J⟩` of (3.156) is absent throughout (zero source);
that is the separately named residual of `DeltaKSuTwoAssembly` §3.

**(b) THE DISPATCHED TARGET IS REFUTED IN THE KERNEL — `[CSTAR-LEVEL-MISMATCH]`.** The natural
composition `γ''·bondEnergy B̃ ≤ CStarDeltaKCCompose.cStarDeltaKCForm a 2 levels U (fullCLM …) B̃`
is **false**, not merely unproved: `cStarDeltaKC_coercivity_refuted` (§5b) proves that for EVERY
`γ > 0`, every `a`, and every background `U`, the inequality FAILS at `B̃ = witA` on `witL5` with
`levels = oneLevelUniv`. Mechanism: `cStarDeltaKCForm … C B̃` unfolds to `deltaKSuTwoForm … (C B̃)`,
which **vanishes identically** on `V = gaugeConstraintSubspaceCovFaithful ell levels U
= {v : Q₁(U)v = 0 ∧ R(D_U^*v) = 0}` (`DeltaKSuTwoAssembly.deltaKSuTwoForm_eq_zero_of_mem_V`, already
in the tree); `fullC` was built precisely to land in `ker Q₁(U)`, the FIRST clause of `V`
(`fullC_mem_V_of_R`, `cStarDeltaKCForm_fullC_eq_zero_of_R`), and at `levels = oneLevelUniv L` the
second clause is vacuous for every `U`
(`CovariantHjMinimizer.RcovLM_oneLevelUniv_eq_zero`), so the sandwich is IDENTICALLY `0`
(`cStarDeltaKCForm_fullC_eq_zero_oneLevelUniv`) while `bondEnergy witA > 0`.

**The root cause, source-pinned and IMAGE-VERIFIED.** CMP99b p.428 uses TWO DIFFERENT averaging
maps in this one passage. Read directly off the 400 dpi render
`corpus/renders/CMP99b_p428-40.png` (LAW-11; corpus page `corpus/pages/CMP99b_p428.md`,
`verification_status: adjudicated`, agrees):

* (3.156): `⟨B,(QG₁Q*)^{-1}B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩`, and immediately below,
  "This form is considered on the subspace `{B: B=0 on Λ^c, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`";
* (3.159): `… ∫ dB↾_Λ δ(Q₁B) δ_Ax(B) × exp[⟨H₁D̃⁽²⁾(B),J⟩ + ⟨B,g⟩] × Z_k^{-1} ∫ dA δ(QA − B)
  δ_R(RD*A)` — `Q` applied to the FINE field `A`, `Q₁` applied to `B` itself, in the SAME display.

So `Δ_k`'s leading `⟨B,(QG₁Q*)^{-1}B⟩` is the Schur complement over the **`Q`**-fibre, while
(3.157)'s constraint `Q₁B = 0` — the one `C` parametrizes — is one level coarser. In the Lean
encoding there is exactly ONE map (`lineCoarseRestrictCovLM U ell`) doing BOTH jobs: it is the first
clause of `gaugeConstraintSubspaceCovFaithful` (the `Q`-fibre of the Schur complement) AND the
constraint `fullC` solves (the `Q₁` of (3.157)) AND `deltaKSuTwoForm`'s mass. That identification —
which `CStarDeltaKCCompose`'s header records approvingly as the "NOT (ii)" verdict, "the two `Q₁`'s
are literally the same `LinearMap`" — is the defect, not a feature: `C` annihilates exactly the
coarse data whose Schur complement `Δ_k` is. Closing `[CSTAR-LEVEL-MISMATCH]` requires a SECOND
coarse-graining `Q₁ : Λ → Λ'` distinct from `Q`, and `Δ_k` re-typed as a form on the coarse
(`B`-level) fields. That is not built here and is not claimed.

**(c) CONDITIONAL on `hthr`/`hsmall`** — the exact `α₁`-threshold `96α₁² ≤ γ₀`, stated, not hidden.

**(d) `k`-uniformity is `[UNIF-ALPHA]`**, the standing regularity hypothesis
(`sup_b ‖U_k b − 1‖` uniformly small in `k`, Bałaban (3.35)–(3.36)), NOT proved here. A single scale
carries no `k`; `γ''` and `γ₀` are literals.

**(e) TORUS, `ell = 2`, `4 ≤ L μ`, `2 ∣ L μ + 1`.** Bałaban's Lemma 2.4 setting is `ℤ^d` with
compact support; the torus is a proxy (MEMORY: `torus-blockOf-truncation-artifact`). The
divisibility hypothesis is exactly what prevents `blockOf` truncation.

**(f) NON-VACUITY — RESOLVED here, and NOT only at `B̃ = 0`.** §6 exhibits `B̃ := witA` on
`witL5` (`L μ = 5`) at `U = trivialU`: `RegularUDomainWitness.witA` is nonzero, axial-gauge, and
(new here, `witA_no_dropped`) vanishes on EVERY dropped bond, with `0 < bondEnergy witA`. So
`cStarDstarDC_coercive_at_witA` is a strictly non-trivial instance. Both `B̃`-hypotheses of §3 are
`U`-FREE, so `witA` satisfies them for every background (`witA_hyps_all_U`); what remains
`U`-dependent is only `hthr`/`hsmall`, i.e. the smallness of `α₁`.
**`[REGU-DOMAIN-NONVAC-GENERALU]` is CLOSED here** (§6b, `regularU_domain_nonvacuous_generalU`):
for EVERY `U`, with no smallness hypothesis at all, `fullC U 2 (dinvC U 2) witA` is a NONZERO
element of `axial-gauge ∩ ker Q₁(U)` with `0 < bondEnergy`. This is exactly the route
`RegularUCoercivityFull`'s docstring named ("`fullC B̃ ∈ ker Q₁(U)` BY CONSTRUCTION; named, not
built") — built now.

**(g) NOT FULL3D, NOT the mass gap, NOT Bałaban's complete theorem.** This is one single-scale
brick. **ISLAND** — nothing here is wired to `coerc_u_main` or any consumed spine declaration;
`build_all_modules.sh` enumerates by `find`, so the module is gated, but it has no consumer.

## Residuals, named

* `[CSTAR-LEVEL-MISMATCH]` (NEW, opened and characterized here) — the encoded `Δ_k` conflates
  Bałaban's `Q` and `Q₁`. Needs a second coarse-graining and `Δ_k` re-typed on coarse fields.
  §5b proves the current encoding is refuted, so this is a STATEMENT defect, not a proof gap.
* `[CSTAR-SCHUR-GAP]` (NEW, opened and bounded here) — §4 pins the direction
  `Δ_j^{cov}_faithful ≤ D_U^*D_U`; a coercivity of the Schur complement needs a lower bound on the
  MINIMIZED energy, which the single-scale transfer does not supply.
* `[UNIF-ALPHA]` (inherited, unchanged) — `k`-uniform smallness of `α₁`, a hypothesis.
* CMP99b (3.156)'s source term `−2⟨H₁D̃⁽²⁾(B),J⟩` at `J ≠ 0` (inherited, `DeltaKSuTwoAssembly` §3).
* `[REGU-DOMAIN-NONVAC-GENERALU]` — **CLOSED here** (§6b).

`#print axioms` on every result below is `{propext, Classical.choice, Quot.sound}` — no `sorry`,
no `native_decide`, no new `axiom`.
-/

namespace AdalyFormal.Balaban.CStarDeltaKCCoercive

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU plaqFnEquiv plaqFnEquiv_symm_apply
  inner_plaqFnL2_eq_covPlaqInner gradCovariantAdjointLM RcovLM PlaqFnL2 deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond)
open AdalyFormal.Balaban.RegularUCoercivityFull (deltaJ_regularU_coercive_on_kerQU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice
  staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.ReparamCSuTwo (coeffDc)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast pathSite_apply_ne)
open AdalyFormal.Balaban.FullReparamC (IsDropped fullC fullCLM fullC_free fullC_mem_kerQ
  fullC_axialGauge solvedValue dinvC dinvC_hinv)
open AdalyFormal.Balaban.DeltaKSuTwoAssembly (deltaKSuTwoForm deltaKSuTwoForm_eq_zero_of_mem_V)
open AdalyFormal.Balaban.CStarDeltaKCCompose (cStarDeltaKCForm covCoarseBondInner_zero)
open AdalyFormal.Balaban.QOne (pathSite)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the ENERGY BRIDGE for the FULL `C`: `bondEnergy B̃ ≤ bondEnergy (fullC B̃)`

The `fullC` analogue of `ReparamCWiring.bondEnergy_reparamCSuTwo_ge` (LAW-19: same mechanism, new
map — `fullC` moves ALL dropped bonds at once, so the single-bond `erase` argument is replaced by a
pointwise comparison). The hypothesis `hdrop` (`B̃` vanishes on every dropped bond) is exactly the
statement that `B̃` is supported on the (3.157) free set `Λ̃`; §1b proves it is NOT droppable. -/

/-- **THE ENERGY BRIDGE.** Termwise: on a free bond `fullC` is the identity; on a dropped bond the
left summand is `0` by `hdrop` and the right one is a square. -/
theorem bondEnergy_le_fullC {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (Btil : Bond L → SuTwo)
    (hdrop : ∀ c : CoarseBond L ell, Btil (droppedBondLast ell c) = 0) :
    bondEnergy Btil ≤ bondEnergy (fullC U ell Dinv Btil) := by
  unfold bondEnergy
  refine Finset.sum_le_sum (fun b _ => ?_)
  by_cases h : IsDropped ell b
  · obtain ⟨c, rfl⟩ := h
    rw [hdrop c, norm_zero]
    have hsq : (0 : ℝ) ≤ ‖fullC U ell Dinv Btil (droppedBondLast ell c)‖ ^ 2 := sq_nonneg _
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact hsq
  · rw [fullC_free U Dinv Btil h]

#print axioms bondEnergy_le_fullC

/-! ### §1b — FALSIFIABILITY CONTROL: `hdrop` is LOAD-BEARING

Without `hdrop` the bridge is FALSE. Concrete refutation: take `Dinv := 0` (a legitimate value of
the `Dinv` argument of `fullC` — the bridge quantifies over ALL `Dinv`, and does not mention
`hinv`), and the field supported on the single dropped bond `droppedBondLast ell c₀`. Then `fullC`
sends it to `0` while its own energy is `‖suTwoWitness‖² > 0`. -/

/-- With `Dinv = 0`, `fullC` annihilates a field supported on one dropped bond. -/
theorem fullC_zeroDinv_single_dropped {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c₀ : CoarseBond L ell) :
    fullC U ell (fun _ => 0) (Pi.single (droppedBondLast ell c₀) suTwoWitness)
      = (0 : Bond L → SuTwo) := by
  funext b
  by_cases h : IsDropped ell b
  · obtain ⟨c, rfl⟩ := h
    rw [AdalyFormal.Balaban.FullReparamC.fullC_dropped hell hdvd U _ _ c, Pi.zero_apply]
    simp [solvedValue]
  · rw [fullC_free U _ _ h, Pi.zero_apply]
    refine Pi.single_eq_of_ne ?_ _
    rintro rfl
    exact h ⟨c₀, rfl⟩

/-- **THE CONTROL FIRES.** Drop `hdrop` and `bondEnergy_le_fullC` is false. -/
theorem bondEnergy_le_fullC_fails_without_hdrop {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c₀ : CoarseBond L ell) :
    ¬ (bondEnergy (Pi.single (droppedBondLast ell c₀) suTwoWitness)
        ≤ bondEnergy (fullC U ell (fun _ => 0)
            (Pi.single (droppedBondLast ell c₀) suTwoWitness))) := by
  rw [fullC_zeroDinv_single_dropped hell hdvd U c₀]
  have hzero : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold bondEnergy; simp
  rw [hzero]
  refine not_le.mpr ?_
  have hle : ‖(Pi.single (droppedBondLast ell c₀) suTwoWitness :
      Bond L → SuTwo) (droppedBondLast ell c₀)‖ ^ 2
      ≤ ∑ b : Bond L, ‖(Pi.single (droppedBondLast ell c₀) suTwoWitness :
        Bond L → SuTwo) b‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun b : Bond L => ‖(Pi.single (droppedBondLast ell c₀) suTwoWitness :
        Bond L → SuTwo) b‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ _)
  have hpos : (0 : ℝ) < ‖(Pi.single (droppedBondLast ell c₀) suTwoWitness :
      Bond L → SuTwo) (droppedBondLast ell c₀)‖ ^ 2 := by
    rw [Pi.single_eq_same]
    have : (0 : ℝ) < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
    positivity
  unfold bondEnergy
  linarith

#print axioms fullC_zeroDinv_single_dropped
#print axioms bondEnergy_le_fullC_fails_without_hdrop

/-! ## §2 — the `C*(D*D)C` sandwich on the free coordinates, and the vanishing of its mass -/

/-- **`⟨B̃, C*(D_U^*D_U − a Q₁^*Q₁)C B̃⟩` for the FULL (3.157) `C`.** The substitution `B = C B̃`
into the (3.10) leading form `‖D_U B‖²` minus the (3.156) averaging mass `a⟨Q₁B,Q₁B⟩`. This is the
`C*(·)C` sandwich over the **leading** term — see the module docstring (a) for why it is NOT
`CStarDeltaKCCompose.cStarDeltaKCForm` (whose leading term is the Schur complement). -/
noncomputable def cStarDstarDCForm (a : ℝ) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (Btil : Bond L → SuTwo) : ℝ :=
  dstarDQuadForm U (fullC U ell Dinv Btil)
    - a * covCoarseBondInner (lineCoarseRestrictCovLM U ell (fullC U ell Dinv Btil))
        (lineCoarseRestrictCovLM U ell (fullC U ell Dinv Btil))

/-- `Q₁(U)(C B̃) = 0` as a FULL coarse field (all coarse bonds simultaneously) — `fullC_mem_kerQ`
repackaged as a function equation. -/
theorem lineCoarseRestrictCovLM_fullC {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo) :
    lineCoarseRestrictCovLM U ell (fullC U ell Dinv Btil) = 0 := by
  funext c
  rw [Pi.zero_apply, lineCoarseRestrictCovLM_apply]
  exact fullC_mem_kerQ hell hdvd U Dinv hinv Btil c

/-- **THE MASS VANISHES IDENTICALLY on the image of the full `C`** — so `cStarDstarDCForm` is
independent of `a`, and the coercivity constant below carries no `a`. This is the (i) collapse of
`CStarDeltaKCCompose`, realized for the FULL `C`. -/
theorem cStarDstarDCForm_eq_dstarD (a : ℝ) {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo) :
    cStarDstarDCForm a ell U Dinv Btil = dstarDQuadForm U (fullC U ell Dinv Btil) := by
  unfold cStarDstarDCForm
  rw [lineCoarseRestrictCovLM_fullC hell hdvd U Dinv hinv Btil, covCoarseBondInner_zero]
  ring

#print axioms lineCoarseRestrictCovLM_fullC
#print axioms cStarDstarDCForm_eq_dstarD

/-! ## §3 — THE HEADLINE: `C*(D_U^*D_U)C ≥ γ''` on the free (3.157) coordinates -/

/-- **THE `C*(D*D)C` COERCIVITY, in the free coordinates `B̃`.**

Hypotheses on `B̃` ALONE: the su(2) axial gauge (`hax`) and vanishing on every dropped bond
(`hdrop`) — together, "`B̃` is supported on the (3.157) free set `Λ̃`". Hypotheses on `U`: the two
`α₁`-smallness bounds `hthr`/`hsmall` (`α₁ = frobSupBond U`). Then for EVERY `a : ℝ`

  `(√(γ₀ − 64α₁²) − 4√2·α₁)² · bondEnergy B̃ ≤ cStarDstarDCForm a 2 U Dinv B̃`,
  `γ₀ = (1/108)(1/2⁴)`.

The chain: `fullC_axialGauge` + `fullC_mem_kerQ` place `C B̃` in `axial-gauge ∩ ker Q₁(U)`, the
domain of `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`; that gives
`γ''·bondEnergy (C B̃) ≤ ‖D_U(C B̃)‖²`; §1's energy bridge gives
`bondEnergy B̃ ≤ bondEnergy (C B̃)`;
§2 identifies `cStarDstarDCForm = ‖D_U(C B̃)‖²`.

**Read the module docstring before quoting this.** It is the LEADING `D*D` term (a), the encoded
`Δ_k` version is refuted (b), it is conditional (c)–(e), and it is one single-scale brick (g). -/
theorem cStarDstarDC_coercive
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (a : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L 2 → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L 2,
      (coeffDc U 2 c (droppedBondLast 2 c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo)
    (hax : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' 2 →
      ∀ e ∈ staircasePath y' x, Btil e = 0)
    (hdrop : ∀ c : CoarseBond L 2, Btil (droppedBondLast 2 c) = 0)
    (hthr : 64 * frobSupBond U ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4))
    (hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond U) :
    (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 * bondEnergy Btil
      ≤ cStarDstarDCForm a 2 U Dinv Btil := by
  have hker := fullC_mem_kerQ (by norm_num) hdvd U Dinv hinv Btil
  have haxC := fullC_axialGauge (by norm_num) hdvd U Dinv Btil hax
  have key := deltaJ_regularU_coercive_on_kerQU hL hdvd U (fullC U 2 Dinv Btil) haxC hker hthr
    hsmall
  have henergy := bondEnergy_le_fullC U Dinv Btil hdrop
  rw [cStarDstarDCForm_eq_dstarD a (by norm_num) hdvd U Dinv hinv Btil]
  refine le_trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)) key

#print axioms cStarDstarDC_coercive

/-! ## §4 — `[CSTAR-SCHUR-GAP]`: the Schur complement is SMALLER, so the bound does not transfer

`deltaJQuadFormCovFaithful ell levels U A0 = ‖curl_U A0 − P_W(curl_U A0)‖²` with `P_W` the
orthogonal projection onto `W = curl_U(V)` (`curlCov_hjExtensionCovFaithful` +
`hjCorrectionTargetCovFaithful`). An orthogonal projection can only REMOVE energy, so the Schur
complement is bounded ABOVE by the raw `‖D_U A0‖²` — the direction that makes a transfer of §3's
lower bound impossible. Proved in the kernel, not asserted.

**⚠ ANNOTATED 2026-07-27 (S75, propagated by the main loop — the answering lane could not edit this
file). The ordering STANDS; the question it was blocking is now ANSWERED, and the answer is not the one
this section anticipated.**

`ThirdLevelSchurGap.schur_le_raw_at_split` re-proves this same inequality at EVERY `LevelSplit` and every
`U`. So the honest finding is stronger than "the bound does not transfer at the collapsed typing": the
ordering is **level-independent**, Pythagoras gives it at every level pair, and **no re-typing reverses
it.** Anyone hoping a genuine two-level split would flip the inequality should stop — that hope is now
refuted, not merely untested.

What the split changes is that the ordering becomes **irrelevant**, because the transfer never needed to
run downward:
- The only lower-bound mechanism is duality, proved SHARP by `CStarLevelCorrected` §3b.
- In the collapsed typing that mechanism is **identically dead** — `collapsed_pairing_dead` and
  `collapsed_factoring_dead` show every admissible witness pairs to `0` and every factoring functional
  kills `Q(fullC B̃)`. That is this module's own refutation, seen from the transfer side.
- At a genuine split it fires **upward**, quantitatively: `deltaJ_ge_dual_pairing_sq`
  (`⟪u, D_U B⟫²/⟪u,u⟫ ≤ Δ_k`, every `U`) and, at `U = 1` for general `ell`,
  `deltaJ_ge_coarse_curl_sq` — a CMP96-(2.128)-shaped domination whose input the `ell₁` constraint does
  NOT kill when `ell < ell₁`. Instantiated at `(2,4)` it gives the explicit `1/64`.

Note where that leaves the recursion: the upward bound's INPUT is the next level's Lemma 2.4, which is
exactly the object gated to grade 3 on 2026-07-27 — and whose obstruction both blind gates narrowed to
PER-BLOCK constants, leaving the region-summed form untested. So this section's successor question is no
longer "can the bound transfer down" but "does Lemma 2.4 hold at the next level in the region-summed
form the upward bound consumes". -/

/-- **`Δ_j^{cov}_faithful ≤ D_U^*D_U`** — the Schur/minimized curl energy never exceeds the raw curl
energy. Pythagoras against `Submodule.starProjection_inner_eq_zero`. -/
theorem deltaJQuadFormCovFaithful_le_dstarDQuadForm (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful ell levels U A0 ≤ dstarDQuadForm U A0 := by
  set K := curlImageCovHFaithful ell levels U with hK
  set x : PeriodicLatticePlaquette L → SuTwo := curlCovariantLM U A0 with hxdef
  set xL : PlaqFnL2 L := WithLp.toLp 2 x with hxL
  -- the correction target, transported into `PlaqFnL2`
  have hy : WithLp.toLp 2 (hjCorrectionTargetCovFaithful ell levels U A0)
      = xL - K.starProjection xL := by
    show WithLp.toLp 2 (x - plaqFnEquiv L (K.starProjection (WithLp.toLp 2 x)))
      = WithLp.toLp 2 x - K.starProjection (WithLp.toLp 2 x)
    rw [show (WithLp.toLp 2 (x - plaqFnEquiv L (K.starProjection (WithLp.toLp 2 x))) :
      PlaqFnL2 L) = WithLp.toLp 2 x - WithLp.toLp 2
        (plaqFnEquiv L (K.starProjection (WithLp.toLp 2 x))) from rfl]
    congr 1
  -- both sides as squared norms in `PlaqFnL2`
  have hlhs : deltaJQuadFormCovFaithful ell levels U A0 = ‖xL - K.starProjection xL‖ ^ 2 := by
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful, ← inner_plaqFnL2_eq_covPlaqInner, hy,
      real_inner_self_eq_norm_sq]
  have hrhs : dstarDQuadForm U A0 = ‖xL‖ ^ 2 := by
    unfold dstarDQuadForm
    rw [← inner_plaqFnL2_eq_covPlaqInner, real_inner_self_eq_norm_sq]
    rfl
  rw [hlhs, hrhs]
  -- Pythagoras
  have hperp : (inner ℝ (xL - K.starProjection xL) (K.starProjection xL) : ℝ) = 0 :=
    Submodule.starProjection_inner_eq_zero xL _ (Submodule.starProjection_apply_mem _ _)
  have hsum : (xL - K.starProjection xL) + K.starProjection xL = xL := by abel
  have hpy := norm_add_sq_real (xL - K.starProjection xL) (K.starProjection xL)
  rw [hsum, hperp] at hpy
  nlinarith [sq_nonneg ‖K.starProjection xL‖]

#print axioms deltaJQuadFormCovFaithful_le_dstarDQuadForm

/-- **The gap, stated at the composed object.** The encoded `Δ_k`-sandwich on the free coordinates
is bounded ABOVE by the leading-term sandwich proved coercive in §3. The lower bound therefore does
NOT descend to `cStarDeltaKCForm`; `[CSTAR-SCHUR-GAP]`. -/
theorem cStarDeltaKCForm_fullC_le_cStarDstarDCForm (a : ℝ) {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo) :
    cStarDeltaKCForm a ell levels U (fullCLM U ell Dinv) Btil
      ≤ cStarDstarDCForm a ell U Dinv Btil := by
  rw [cStarDstarDCForm_eq_dstarD a hell hdvd U Dinv hinv Btil]
  show deltaKSuTwoForm a ell levels U (fullCLM U ell Dinv Btil) ≤ _
  unfold deltaKSuTwoForm
  rw [show fullCLM U ell Dinv Btil = fullC U ell Dinv Btil from rfl,
    lineCoarseRestrictCovLM_fullC hell hdvd U Dinv hinv Btil, covCoarseBondInner_zero]
  have := deltaJQuadFormCovFaithful_le_dstarDQuadForm (L := L) ell levels U
    (fullC U ell Dinv Btil)
  linarith

#print axioms cStarDeltaKCForm_fullC_le_cStarDstarDCForm

/-! ## §5 — `[CSTAR-LEVEL-MISMATCH]`: the encoded `C*Δ_kC` sandwich COLLAPSES TO ZERO

`fullC` was built to land in `ker Q₁(U)`, which is the FIRST of the two clauses defining the gauge
kernel `V` on which `deltaKSuTwoForm` vanishes identically. Only the `R`-clause stands between the
composition and identical vanishing. This is the sharp, machine-checked form of the refutation in
docstring item (b): wherever the `R`-clause holds, no positive constant can bound the encoded
sandwich below by a positive multiple of `bondEnergy B̃`. -/

/-- **The `ker Q₁` clause of `V` is FREE for `fullC`.** -/
theorem fullC_mem_V_of_R {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo)
    (hR : RcovLM U levels (gradCovariantAdjointLM U (fullC U ell Dinv Btil)) = 0) :
    fullC U ell Dinv Btil ∈ gaugeConstraintSubspaceCovFaithful ell levels U :=
  mem_gaugeConstraintSubspaceCovFaithful.mpr
    ⟨lineCoarseRestrictCovLM_fullC hell hdvd U Dinv hinv Btil, hR⟩

/-- **THE COLLAPSE, PROVED.** If the `R`-clause holds at `C B̃`, the encoded `C*Δ_kC` sandwich is
`0` — for every `a`, every `levels`, every `B̃`. Since `bondEnergy B̃ > 0` is available (§6), no
`γ > 0` can satisfy `γ · bondEnergy B̃ ≤ cStarDeltaKCForm …` there. -/
theorem cStarDeltaKCForm_fullC_eq_zero_of_R (a : ℝ) {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo)
    (hR : RcovLM U levels (gradCovariantAdjointLM U (fullC U ell Dinv Btil)) = 0) :
    cStarDeltaKCForm a ell levels U (fullCLM U ell Dinv) Btil = 0 :=
  deltaKSuTwoForm_eq_zero_of_mem_V a ell levels U (fullC U ell Dinv Btil)
    (fullC_mem_V_of_R hell hdvd levels U Dinv hinv Btil hR)

#print axioms fullC_mem_V_of_R
#print axioms cStarDeltaKCForm_fullC_eq_zero_of_R

/-! ### §5b — the collapse made UNCONDITIONAL at an explicit `levels`, and the REFUTATION

`hR` is not a side condition one has to hope for: at `levels = oneLevelUniv L = [(1, univ)]` the
gauge-fixing map is the ZERO map for EVERY `U` (`CovariantHjMinimizer.RcovLM_oneLevelUniv_eq_zero`,
already in the tree — LAW-19), so `hR` holds identically. `oneLevelUniv` is a legitimate member of
the `levels` family the target quantifies over ("`λ = 0` on `Λ₀`" at level `0`), so a refutation
there refutes the target as stated. -/

/-- **THE COLLAPSE, UNCONDITIONAL** at `levels = oneLevelUniv L`: for EVERY `a`, `U`, `Dinv` with
`hinv`, and EVERY `B̃`, the encoded `C*Δ_kC` sandwich on the free coordinates is `0`. -/
theorem cStarDeltaKCForm_fullC_eq_zero_oneLevelUniv (a : ℝ) {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L)).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L) U).HasOrthogonalProjection]
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (Btil : Bond L → SuTwo) :
    cStarDeltaKCForm a ell (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L) U
        (fullCLM U ell Dinv) Btil = 0 :=
  cStarDeltaKCForm_fullC_eq_zero_of_R a hell hdvd _ U Dinv hinv Btil
    (AdalyFormal.Balaban.CovariantHjMinimizer.RcovLM_oneLevelUniv_eq_zero U _)

/-- **THE DISPATCHED TARGET IS REFUTED.** No positive constant `γ` — in particular not
`γ'' = (√(γ₀ − 64α₁²) − 4√2α₁)²`, which at `U = trivialU` is `γ₀ = (1/108)(1/2⁴) > 0` — can bound
the encoded `C*Δ_kC` sandwich below by `γ · bondEnergy B̃` on the free coordinates: at
`B̃ = witA` on `witL5` the sandwich is `0` while `bondEnergy witA > 0`.

This is the machine-checked content of `[CSTAR-LEVEL-MISMATCH]`. It refutes the STATEMENT, not the
mathematics: §3's `cStarDstarDC_coercive` — the same sandwich over the LEADING `D*D` term — is true
and proved. The defect is that the encoded `Δ_k` reuses ONE map for Bałaban's `Q` (the Schur fibre,
`δ(QA − B)` in (3.159)) and his `Q₁` (the (3.157) constraint, `δ(Q₁B)` in the same display), so the
reparametrization `C` annihilates exactly the coarse data whose Schur complement `Δ_k` is. -/
theorem cStarDeltaKC_coercivity_refuted (a γ : ℝ) (hγ : 0 < γ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      RegularUDomainWitness.witL5)
    [(deltaKernelImageCovH U (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv
      RegularUDomainWitness.witL5)).HasOrthogonalProjection]
    [(curlImageCovHFaithful 2 (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv
      RegularUDomainWitness.witL5) U).HasOrthogonalProjection] :
    ¬ (γ * bondEnergy RegularUDomainWitness.witA
        ≤ cStarDeltaKCForm a 2
            (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv RegularUDomainWitness.witL5) U
            (fullCLM U 2 (dinvC U 2)) RegularUDomainWitness.witA) := by
  rw [cStarDeltaKCForm_fullC_eq_zero_oneLevelUniv a (by norm_num)
    RegularUDomainWitness.witL5_two_dvd U (dinvC U 2)
    (dinvC_hinv (by norm_num) RegularUDomainWitness.witL5_two_dvd U)
    RegularUDomainWitness.witA]
  refine not_le.mpr ?_
  exact mul_pos hγ RegularUDomainWitness.bondEnergy_witA_pos

#print axioms cStarDeltaKCForm_fullC_eq_zero_oneLevelUniv
#print axioms cStarDeltaKC_coercivity_refuted

/-! ## §6 — NON-VACUITY: a NONZERO `B̃` satisfying every hypothesis on `B̃`, for EVERY `U`

`RegularUDomainWitness.witA` on `witL5` (`L μ = 5`, so `4 ≤ 5` ✓ and `2 ∣ 6` ✓) is nonzero, has
strictly positive `bondEnergy`, and satisfies the axial gauge. What is NEW here is that it also
vanishes on every dropped bond — so it satisfies BOTH `B̃`-hypotheses of §3, and it does so for
EVERY background `U` (neither hypothesis mentions `U`). -/

/-- **No dropped bond is a direction-`0` bond whose coordinate `2` is `5`.** A dropped bond
`droppedBondLast 2 c = (pathSite c₋ c.2 1, c.2)` in direction `c.2 = 0` leaves coordinate `2`
untouched, so its coordinate `2` is that of the coarse site `c₋`, which is even; `5` is odd. Both
`witA`'s support bonds (`bPlus = ((5,5,5),0)`, `bMinus = ((5,4,5),0)`) are of this shape. -/
theorem droppedBondLast_ne_dir0_top (c : CoarseBond RegularUDomainWitness.witL5 2)
    (s : PeriodicLatticeSite RegularUDomainWitness.witL5) (hs : (s 2).val = 5) :
    droppedBondLast 2 c ≠ (s, (0 : Fin 3)) := by
  intro heq
  have hdir : c.2 = (0 : Fin 3) := congrArg Prod.snd heq
  have hsite : (droppedBondLast 2 c).1 = s := congrArg Prod.fst heq
  have h2 : ((droppedBondLast 2 c).1 2).val % 2 = 0 := by
    show ((pathSite c.1.1 c.2 (2 - 1)) 2).val % 2 = 0
    rw [hdir, pathSite_apply_ne _ 0 2 (2 - 1) (by decide)]
    exact mem_CoarseLattice.mp c.1.2 2
  rw [hsite, hs] at h2
  omega

/-- **`witA` vanishes on every dropped bond.** -/
theorem witA_no_dropped :
    ∀ c : CoarseBond RegularUDomainWitness.witL5 2,
      RegularUDomainWitness.witA (droppedBondLast 2 c) = 0 := by
  intro c
  have hP : droppedBondLast 2 c ≠ RegularUDomainWitness.bPlus :=
    droppedBondLast_ne_dir0_top c _ (by decide)
  have hM : droppedBondLast 2 c ≠ RegularUDomainWitness.bMinus :=
    droppedBondLast_ne_dir0_top c _ (by decide)
  show RegularUDomainWitness.witChi (droppedBondLast 2 c) • suTwoWitness = 0
  have : RegularUDomainWitness.witChi (droppedBondLast 2 c) = 0 := by
    simp [RegularUDomainWitness.witChi, hP, hM]
  rw [this, zero_smul]

/-- **Both `B̃`-hypotheses of §3, satisfied by a NONZERO field, for EVERY `U`.** -/
theorem witA_hyps_all_U :
    (∀ y' : PeriodicLatticeSite RegularUDomainWitness.witL5,
        y' ∈ CoarseLattice RegularUDomainWitness.witL5 2 →
        ∀ x : PeriodicLatticeSite RegularUDomainWitness.witL5, x ∈ blockOf y' 2 →
        ∀ e ∈ staircasePath y' x, RegularUDomainWitness.witA e = 0) ∧
      (∀ c : CoarseBond RegularUDomainWitness.witL5 2,
        RegularUDomainWitness.witA (droppedBondLast 2 c) = 0) ∧
      RegularUDomainWitness.witA ≠ 0 ∧ 0 < bondEnergy RegularUDomainWitness.witA :=
  ⟨RegularUDomainWitness.witA_axial, witA_no_dropped, RegularUDomainWitness.witA_ne_zero,
    RegularUDomainWitness.bondEnergy_witA_pos⟩

/-- **§3 INSTANTIATED, with a strictly positive left-hand side.** At `U = trivialU`,
`α₁ = frobSupBond (trivialU) = 0`, both smallness hypotheses are trivial and the constant collapses
to `γ₀ = (1/108)(1/2⁴)`:

  `γ₀ · bondEnergy witA ≤ cStarDstarDCForm a 2 (trivialU witL5) (dinvC …) witA`,
  `0 < bondEnergy witA`,

for EVERY `a : ℝ`. So the headline is not the vacuous `0 ≤ …`. -/
theorem cStarDstarDC_coercive_at_witA (a : ℝ) :
    (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) * bondEnergy RegularUDomainWitness.witA
        ≤ cStarDstarDCForm a 2 (trivialU RegularUDomainWitness.witL5)
            (dinvC (trivialU RegularUDomainWitness.witL5) 2) RegularUDomainWitness.witA
      ∧ 0 < bondEnergy RegularUDomainWitness.witA := by
  refine ⟨?_, RegularUDomainWitness.bondEnergy_witA_pos⟩
  have hα : frobSupBond (trivialU RegularUDomainWitness.witL5) = 0 :=
    RegularUDomainWitness.frobSupBond_trivialU RegularUDomainWitness.witL5
  have hγ0 : (0 : ℝ) ≤ (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by norm_num
  have hthr : 64 * frobSupBond (trivialU RegularUDomainWitness.witL5) ^ 2
      ≤ (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by rw [hα]; norm_num
  have hsmall : 0 ≤ Real.sqrt ((1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4)
        - 64 * frobSupBond (trivialU RegularUDomainWitness.witL5) ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond (trivialU RegularUDomainWitness.witL5) := by
    rw [hα]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
    positivity
  have key := cStarDstarDC_coercive RegularUDomainWitness.witL5_four_le
    RegularUDomainWitness.witL5_two_dvd a (trivialU RegularUDomainWitness.witL5)
    (dinvC (trivialU RegularUDomainWitness.witL5) 2)
    (dinvC_hinv (by norm_num) RegularUDomainWitness.witL5_two_dvd
      (trivialU RegularUDomainWitness.witL5))
    RegularUDomainWitness.witA RegularUDomainWitness.witA_axial witA_no_dropped hthr hsmall
  rw [hα] at key
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at key
  rwa [Real.sq_sqrt hγ0] at key

#print axioms droppedBondLast_ne_dir0_top
#print axioms witA_no_dropped
#print axioms witA_hyps_all_U
#print axioms cStarDstarDC_coercive_at_witA

/-! ### §6b — `[REGU-DOMAIN-NONVAC-GENERALU]` CLOSED

The residual left open by `RegularUCoercivityFull` was: is `axial-gauge ∩ ker Q₁(U)` nontrivial at a
FIXED NON-TRIVIAL `U`? Its own docstring named the intended route — "the `C`-reparametrization
(`fullC B̃ ∈ ker Q₁(U)` BY CONSTRUCTION); named, not built". It is built now, and the route works
with NO smallness hypothesis and NO restriction on `U`: `fullC U 2 (dinvC U 2) witA` is axial-gauge
(`fullC_axialGauge` + `witA_axial`), lies in `ker Q₁(U)` (`fullC_mem_kerQ` + `dinvC_hinv`), and is
NONZERO — because §1's energy bridge gives `0 < bondEnergy witA ≤ bondEnergy (fullC … witA)`, and
`witA` vanishes on every dropped bond (`witA_no_dropped`), which is exactly the bridge's hypothesis.
The `U`-transport obstruction recorded there (at `U ≠ 1` the `±w` pair carries different
holonomies, so the cancellation does not transport) is bypassed: `fullC` does not transport `witA`'s
cancellation, it RE-SOLVES the constraint at each coarse bond. -/

/-- **A NONZERO element of `axial-gauge ∩ ker Q₁(U)`, for EVERY background `U`** — with strictly
positive bond energy, on the compatible torus `witL5` (`4 ≤ 5`, `2 ∣ 6`), block side `ell = 2`.
Closes `[REGU-DOMAIN-NONVAC-GENERALU]`. -/
theorem regularU_domain_nonvacuous_generalU
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      RegularUDomainWitness.witL5) :
    (∀ y' : PeriodicLatticeSite RegularUDomainWitness.witL5,
        y' ∈ CoarseLattice RegularUDomainWitness.witL5 2 →
        ∀ x : PeriodicLatticeSite RegularUDomainWitness.witL5, x ∈ blockOf y' 2 →
        ∀ e ∈ staircasePath y' x,
          fullC U 2 (dinvC U 2) RegularUDomainWitness.witA e = 0) ∧
      (∀ b : CoarseBond RegularUDomainWitness.witL5 2,
        lineCoarseRestrictCov U 2 (fullC U 2 (dinvC U 2) RegularUDomainWitness.witA) b = 0) ∧
      0 < bondEnergy (fullC U 2 (dinvC U 2) RegularUDomainWitness.witA) ∧
      fullC U 2 (dinvC U 2) RegularUDomainWitness.witA ≠ 0 := by
  have hE : 0 < bondEnergy (fullC U 2 (dinvC U 2) RegularUDomainWitness.witA) :=
    lt_of_lt_of_le RegularUDomainWitness.bondEnergy_witA_pos
      (bondEnergy_le_fullC U (dinvC U 2) RegularUDomainWitness.witA witA_no_dropped)
  refine ⟨fullC_axialGauge (by norm_num) RegularUDomainWitness.witL5_two_dvd U (dinvC U 2)
      RegularUDomainWitness.witA RegularUDomainWitness.witA_axial,
    fullC_mem_kerQ (by norm_num) RegularUDomainWitness.witL5_two_dvd U (dinvC U 2)
      (dinvC_hinv (by norm_num) RegularUDomainWitness.witL5_two_dvd U)
      RegularUDomainWitness.witA,
    hE, ?_⟩
  intro h0
  rw [h0] at hE
  have : bondEnergy (0 : Bond RegularUDomainWitness.witL5 → SuTwo) = 0 := by
    unfold bondEnergy; simp
  rw [this] at hE
  exact lt_irrefl 0 hE

#print axioms regularU_domain_nonvacuous_generalU

/-! ### §6c — FALSIFIABILITY CONTROL: `hinv` is LOAD-BEARING for the mass collapse

`lineCoarseRestrictCovLM_fullC` and `cStarDstarDCForm_eq_dstarD` both consume `hinv` (the
per-coarse-bond right-inverse property of `Dinv`). Drop it — take `Dinv = 0`, a legitimate value of
the argument — and both FAIL: `fullC` becomes the identity on a field supported off the dropped
bonds, and `RegularUDomainWitness.witASingle` (control A of that module: `witA` with the cancelling
`−` bond deleted) is proved there NOT to lie in `ker Q₁(1)`, with the exact value
`(1/8)·suTwoWitness`. So the mass term is nonzero and the identity `cStarDstarDCForm = dstarD`
breaks. This is a MADE-IT-FAIL control, not an argument that it would fail. -/

/-- `witASingle` also vanishes on every dropped bond (it is `witA` with one term deleted). -/
theorem witASingle_no_dropped :
    ∀ c : CoarseBond RegularUDomainWitness.witL5 2,
      RegularUDomainWitness.witASingle (droppedBondLast 2 c) = 0 := by
  intro c
  have hP : droppedBondLast 2 c ≠ RegularUDomainWitness.bPlus :=
    droppedBondLast_ne_dir0_top c _ (by decide)
  show (if droppedBondLast 2 c = RegularUDomainWitness.bPlus then (1 : ℝ) else 0)
      • suTwoWitness = 0
  rw [if_neg hP, zero_smul]

/-- With `Dinv = 0` (which FAILS `hinv`), `fullC` acts as the identity on `witASingle`. -/
theorem fullC_zeroDinv_witASingle
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      RegularUDomainWitness.witL5) :
    fullC U 2 (fun _ => 0) RegularUDomainWitness.witASingle
      = RegularUDomainWitness.witASingle := by
  funext b
  by_cases h : IsDropped 2 b
  · obtain ⟨c, rfl⟩ := h
    rw [AdalyFormal.Balaban.FullReparamC.fullC_dropped (by norm_num)
      RegularUDomainWitness.witL5_two_dvd U _ _ c, witASingle_no_dropped c]
    simp [solvedValue]
  · rw [fullC_free U _ _ h]

/-- **THE CONTROL FIRES.** Without `hinv`, `fullC`'s image ESCAPES `ker Q₁(U)`. -/
theorem lineCoarseRestrictCovLM_fullC_fails_without_hinv :
    lineCoarseRestrictCov (trivialU RegularUDomainWitness.witL5) 2
        (fullC (trivialU RegularUDomainWitness.witL5) 2 (fun _ => 0)
          RegularUDomainWitness.witASingle) RegularUDomainWitness.cBond ≠ 0 := by
  rw [fullC_zeroDinv_witASingle (trivialU RegularUDomainWitness.witL5)]
  exact RegularUDomainWitness.witASingle_not_mem_kerQ1

/-- **…and therefore the MASS TERM is strictly positive there**, so
`cStarDstarDCForm_eq_dstarD` is false without `hinv`: the mass collapse is genuinely bought by the
right-inverse property, not by the shape of the definition. -/
theorem mass_pos_without_hinv :
    0 < covCoarseBondInner
        (lineCoarseRestrictCovLM (trivialU RegularUDomainWitness.witL5) 2
          (fullC (trivialU RegularUDomainWitness.witL5) 2 (fun _ => 0)
            RegularUDomainWitness.witASingle))
        (lineCoarseRestrictCovLM (trivialU RegularUDomainWitness.witL5) 2
          (fullC (trivialU RegularUDomainWitness.witL5) 2 (fun _ => 0)
            RegularUDomainWitness.witASingle)) := by
  refine covCoarseBondInner_pos_of_ne ?_
  intro h0
  refine lineCoarseRestrictCovLM_fullC_fails_without_hinv ?_
  have := congrFun h0 RegularUDomainWitness.cBond
  rwa [Pi.zero_apply, lineCoarseRestrictCovLM_apply] at this

#print axioms witASingle_no_dropped
#print axioms fullC_zeroDinv_witASingle
#print axioms lineCoarseRestrictCovLM_fullC_fails_without_hinv
#print axioms mass_pos_without_hinv

end AdalyFormal.Balaban.CStarDeltaKCCoercive
