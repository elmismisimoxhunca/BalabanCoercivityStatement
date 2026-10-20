/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CStarDeltaKCCoercive

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `CStarLevelCorrected.lean` — the RE-TYPING that repairs `[CSTAR-LEVEL-MISMATCH]`

## The defect this module repairs

`CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` proves in the kernel that the encoded
`C*Δ_kC` target is **identically zero** on nonzero data. The mechanism is a LEVEL COLLAPSE: one and
the same Lean map, `lineCoarseRestrictCovLM U ell`, was playing two roles that CMP99b p.428 keeps
one renormalisation level apart.

**Source characterisation** (600 dpi renders + verbatim quotes:
`compute/cstar_level_fix/CHARACTERIZATION.md`, renders `compute/cstar_level_fix/*.png`; printed
pages confirmed in the render's own running head; `corpus/tools/page_offsets.json` offsets 388
(CMP99b) and 222 (CMP96), both `constant_verified`):

* CMP99b p.428 (3.159) carries **both maps in one display**:
  `∫ dB↾_Λ δ(Q₁B) δ_Ax(B) × exp[…] × Z_k^{-1} ∫ dA δ(QA − B) δ_R(RD*A) × exp[−½⟨A,(Δ+Δ⁽²⁾)A⟩]`.
  `Q` is applied to the FINE `A` (the Schur fibre, `QA = B`); `Q₁` is applied to `B` itself.
* CMP99b p.393 defines `Q_j(U) = Q(Ū^{j-1})·····Q(Ū)Q(U)`, "*compositions of `j` one-step
  averaging*" operators; §E (p.427) fixes `Λ ⊂ Λ_k = Ω_k^{(k)}` as a domain **of the unit lattice**.
  So `Q = Q_k(U) : fine → unit`.
* CMP96 (`[4]`) p.245 DEFINES the other map:
  `(Q₁B)(c) = Σ_{x∈B(c_-)} L^{-(d+1)} B([x, x+Le_μ])`, indexed by `c ∈ Λ'`. Its argument is a
  unit-lattice bond field, its output lives on `Λ'`. CMP99b p.431 independently confirms the
  codomain: "`Q₁'v = 0` **on `Λ'`**".
* CMP99b p.428 (3.156): `⟨B,(QG₁Q*)^{-1}B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩`, "*This form is
  considered on the subspace `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'}Ax(y), Q₁B=0}`*", and `B = C B̃` with
  `C` solving one equation per coarse bond `c ∈ Λ'`.

**HOW TO SAY THIS CORRECTLY (revised 2026-07-26; an earlier draft of this docstring said "`Q ≠ Q₁`,
two different maps" and that is the wrong framing).** CMP99b p.393 (3.15) defines
`Q_j(U) = Q(Ū^{j-1})⋯Q(Ū)Q(U)`, so **`Q₁(U) = Q(U)`**: the subscript `1` is the `j = 1` member of the
family, a SINGLE application — not a different operator. There is ONE construction, applied at TWO
LEVELS: `Q = Q_k` eats the fine `A` and lands on the unit lattice; `Q₁` eats the unit `B` and lands
on `Λ'`. **One operator, two arrows.** The source display is well-typed because it is one operator;
the encoding is refuted because the two arrows were identified. Building a *second, different*
coarse-graining would encode a distinction the source does not make.

This also settles a contradiction the tree carries unreconciled: `Balaban/BackgroundAveraging.lean`
banks `Q₁(U) = Q(U)` (correct, adopted here), while `Balaban/CovarianceG1.lean` §0c banks `Q₁` as "a
genuinely distinct, currently-UNLOCATED seventh ingredient" on the grounds that its arithmetic is
not spelled out in pp.421–430. The observation is true; the verdict is **SUPERSEDED** — `Q₁` is not
respelled there because it was already defined on p.393, and its arithmetic is written out in `[4]`
= CMP96 p.245. (Reported for S75 propagation, not edited — write-scope.)

**One further refinement of the dispatched diagnosis:** the source puts the MASS at the `Q` level,
not the `Q₁` level — `a⟨B,B⟩` in (3.156) is the norm of the unit field `B = QA`. So the correct
grouping is `{fibre, mass}` at `Q` and `{(3.157) constraint}` at `Q₁`; only the constraint sat at the
wrong level. (In the source the `−a⟨B,B⟩` is in fact cancelled by the `Q*aQ` term inside
`Δ + Δ⁽²⁾`, so the faithful `Δ_k` is the `a`-free Schur complement of the curl energy — the same
conclusion `CStarDeltaKCCompose`'s header reached independently.)

**WHICH HALF OF THE TREE IS MIS-LEVELLED.** `lineCoarseRestrictCov U ell` reproduces CMP96 p.245's
`(Q₁B)(c)` including the `1/ell⁴ = η^{d+1}` weight: it is a **faithful `Q₁`**, and `fullC`/`C` built
on it are **correct**. What has **no Lean object at all** is `Q` as a map from a level FINER than
`Bond L`. The mis-levelled declarations are `gaugeConstraintSubspaceCovFaithful` /
`hjExtensionCovFaithful` / `deltaJQuadFormCovFaithful`, whose docstrings name one and the same
declaration three ways (`Q_k(U)`, `Q_1(U)`, `Q₁(U)`). The structural cause: only TWO lattice levels
exist in this tree and (3.156)–(3.159) needs THREE. **The final repair is a genuine third level** —
a finer bond space with `Q : finer → Bond L`, `Δ_k`'s Schur fibre taken there, and `C`'s constraint
left where it is, on `Bond L`. That construction is NOT built here; §6 states what it needs.

In this tree everything is presented pulled back to the fine bond space `Bond L → SuTwo`, and the
whole level tower is indexed by the BLOCK SIDE: `Q_{ell} = lineCoarseRestrictCovLM U ell`. The
corrected typing is therefore **two block sides, not one**:

| source object | level | this tree |
|---|---|---|
| `Q` (Schur fibre of (3.159), and the mass's `B`) | fine → unit | `lineCoarseRestrictCovLM U ell₀` |
| `Q₁` ((3.157)'s constraint, the one `C` solves) | unit → `Λ'` | `lineCoarseRestrictCovLM U ell₁` |
| `Q₁ ∘ Q = Q_{k+1}` | fine → `Λ'` | `ell₁ = ell₀ · m`, `m ≥ 2` |

`LevelSplit` (§1) makes `ell₀ = ell₁` **unstateable**: the collapse cannot be re-introduced by
accident. `ell₀ ∣ ell₁` and `ell₀ < ell₁` are exactly Bałaban's nested `Q_j` tower.

## What is PROVED here

1. **§2** the corrected objects `deltaKCorr` / `cStarDeltaKCFormCorr` / `massCorr`, typed by a
   `LevelSplit`.
2. **§3** a general, `LevelSplit`-free **duality criterion** for non-degeneracy:
   `deltaKCorr` is strictly positive at `B` as soon as there is a plaquette field `u` orthogonal to
   `D_U(V)` with `⟪u, D_U B⟫ ≠ 0` (`deltaKCorr_pos_of_dual_witness`). **§3b** proves the criterion is
   SHARP — the canonical `u = D_UB − P_W(D_UB)` pairs with `D_UB` to give exactly `Δ_k(B)`
   (`dual_witness_criterion_sharp`), so nothing is lost by working through it. **§3c** reduces it to
   the strictly cheaper, purely combinatorial obligation of exhibiting a pair `(u, φ)` making
   `⟪u, D_U ·⟫` FACTOR THROUGH `Q_{ell₀}` (`deltaKCorr_pos_of_factoring_witness`) — that pair is the
   only thing standing between §5's `ell₀ = 1` witness and the general case, and §6 states exactly
   what it is.
3. **§4** at `ell₀ = 1` (Bałaban's `k = 0`, where `Q_0` is the empty composition, i.e. the identity,
   and `V = ⊥`) the corrected `Δ_k` reduces EXACTLY to the raw `D_U^*D_U` form.
4. **§5 THE NON-DEGENERACY WITNESS** — `corrected_nondegeneracy`. With `ell₀ = 1`, `ell₁ = 2`,
   `U = 1` on the compatible torus `witL5`, `B := fullC U 2 (dinvC U 2) witA`:
   `Q₁ B = 0` (`B` lies in the (3.157) constraint subspace), `B ≠ 0`, and
   `γ₀ · bondEnergy witA ≤ deltaKCorr splitK0 … B`, with `γ₀ = (1/108)(1/2⁴) > 0` and
   `0 < bondEnergy witA`. **So `Δ_k` does NOT vanish identically on `ker Q₁` in the corrected
   typing.** That is exactly the property the collapsed encoding provably lacked.
5. **§5b THE SEPARATION** — `level_split_separates`. Same `U`, same `levels`, same field `B`:
   at the collapsed level `ell₀ = ell₁ = 2` the value is `0`; at the corrected split
   `ell₀ = 1 < 2 = ell₁` it is strictly positive. A one-parameter mutation isolating the defect.
6. **§5c THE MASS IS ALSO REVIVED** — `massCorr` is `0` in the collapsed typing and strictly
   positive in the corrected one, on the same field.

## ⚠ HONEST SCOPE — read before quoting anything above

* **NO COERCIVITY IS CLAIMED.** The deliverable is the corrected typing plus a non-degeneracy
  witness. `C*Δ_kC ≥ γ₀` on the corrected object, uniformly in `k` and `U`, is NOT proved here.
* **⚠ §5's WITNESS SITS AT A DEGENERATE TEST POINT — read this before citing it.** `ell₀ = 1` makes
  `Q_1(U)` injective, hence `V = ⊥`, hence `deltaKCorr = dstarDQuadForm` EXACTLY: the Schur
  complement is not exercised at all. This is the class-5 degenerate-test-point failure mode this
  campaign has been bitten by before (a point where every wrong alternative coincides and the gate
  still reports green). It is a faithful member of the family — it is Bałaban's `k = 0`, and CMP96
  Lemma 2.4, the `U = 1` result p.428 cites for `γ₀`, is itself stated entirely at the unit lattice
  with only `Q₁` and `∂₁` and no fine level — but **a witness there does NOT by itself demonstrate
  that the re-typing repairs the Schur mechanism.** What §5 DOES establish, and all it establishes,
  is that the vanishing proved by `cStarDeltaKC_coercivity_refuted` is caused by the level
  identification and not by the field, the background or the constraint: move the fibre level alone
  and the value is no longer identically zero (§5b). A witness at `ell₀ ≥ 2` is the thing that would
  demonstrate the repair, it is NOT established here, and §3b proves there is no way to it that
  avoids §6's `[STOKES-COMM]`.
* **`levels = oneLevelUniv`** makes the `R`-clause of `V` vacuous
  (`RcovLM_oneLevelUniv_eq_zero`); with a live `R` the subspace `V` is smaller and `Δ_k` is larger,
  so §5's lower bound only improves, but §5b's collapsed `= 0` half is stated for `oneLevelUniv`
  and is not claimed for other `levels`.
* **`J = 0` throughout** — the `−2⟨H₁D̃⁽²⁾(B),J⟩` term of (3.156) is absent, the standing residual
  of `DeltaKSuTwoAssembly` §3.
* ~~**TWO NAMED RESIDUALS, both created here and both stated in §6:**~~ `[STOKES-COMM]` (supplies the
  dual witness for `ell₀ ≥ 2`; reduced in the kernel by §3c to one combinatorial pair `(u, φ)`) and
  `[Q-SEMIGROUP]` (`Q₁ ∘ Q_{ell₀} = Q_{ell₀·m}`, needed only to QUOTE the level table at `ell₀ ≥ 2`;
  discharged trivially at `splitK0`, used by no theorem here).
  **STRUCK 2026-07-30: BOTH ARE CLOSED AT `U = 1`, and this file's own §5 table already says so.**
  `[STOKES-COMM]` → `ThirdLevelStokes.stokes_flat` / `stokes_factoring` (general `ell`);
  `[Q-SEMIGROUP]` → `ThirdLevelArrows.tower_law` + `ker_translation`. Calling them "residuals" in
  the header while the table 420 lines below records them closed is what sent a later lane down a
  ~170-line rebuild — see the fuller note in §6. **Still genuinely open at general covariant `U`, in
  BOTH directions** (`TowerLawCovariant`: not "the tower law is false", not "the tower law holds").
* **Nothing upstream is edited.** `CStarDeltaKCCompose`, `CStarDeltaKCCoercive`, `FullReparamC`,
  `ReparamC*` keep their content, which stays TRUE — about the collapsed object. What was wrong was
  the identification of that object with Bałaban's; §6 lists what each needs.
-/

namespace AdalyFormal.Balaban.CStarLevelCorrected

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU gradCovariantAdjointLM RcovLM
  deltaKernelImageCovH oneLevelUniv RcovLM_oneLevelUniv_eq_zero)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.FullReparamC (fullC dinvC dinvC_hinv)
open AdalyFormal.Balaban.CovariantHjMinimizer (covPlaqInner_add_right)
open AdalyFormal.Balaban.CStarDeltaKCCompose (covCoarseBondInner_zero)
open AdalyFormal.Balaban.CStarDeltaKCCoercive (cStarDstarDCForm cStarDstarDCForm_eq_dstarD
  cStarDstarDC_coercive_at_witA regularU_domain_nonvacuous_generalU fullC_mem_V_of_R
  lineCoarseRestrictCovLM_fullC)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `LevelSplit`: the typing that makes the collapse UNSTATEABLE

A `LevelSplit` is the pair of block sides `(ell₀, ell₁)` realising CMP99b's two distinct averaging
maps. The three fields are exactly the source's own conditions on the `Q_j` tower: `ell₀ > 0`
(a block has sites), `ell₀ ∣ ell₁` (`Q₁ ∘ Q_{ell₀} = Q_{ell₁}`, nested blocks), and `ell₀ < ell₁`
(`Q₁` is a genuine one-step coarse-graining, `m ≥ 2`, NOT the identity). The last field is the
anti-collapse condition: no term of type `LevelSplit` can have `fibre = constr`. -/
structure LevelSplit where
  /-- `ell₀` — the block side of `Q`, CMP99b (3.159)'s `δ(QA − B)`; fine → unit. -/
  fibre : ℕ
  /-- `ell₁` — the block side of `Q₁`, CMP99b (3.155)/(3.157)'s `δ(Q₁B)`; unit → `Λ'`. -/
  constr : ℕ
  fibre_pos : 0 < fibre
  refines : fibre ∣ constr
  proper : fibre < constr

/-- The anti-collapse fact, stated as a theorem so it can be cited: a `LevelSplit`'s two block
sides are never equal. This is the ONE property the refuted encoding violated. -/
theorem LevelSplit.ne (S : LevelSplit) : S.fibre ≠ S.constr := Nat.ne_of_lt S.proper

/-- `0 < ell₁` follows. -/
theorem LevelSplit.constr_pos (S : LevelSplit) : 0 < S.constr := lt_trans S.fibre_pos S.proper

#print axioms LevelSplit.ne
#print axioms LevelSplit.constr_pos

/-! ## §2 — the corrected objects -/

/-- **`Δ_k` at the corrected level.** CMP99b (3.156)'s `⟨B, Δ_kB⟩` with `J = 0`: the Schur
complement of the fine curl energy over the **`Q = Q_{ell₀}`** fibre — `S.fibre`, NOT `S.constr`.
This is `deltaJQuadFormCovFaithful` evaluated at the FIBRE block side. -/
noncomputable def deltaKCorr (S : LevelSplit) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) : ℝ :=
  deltaJQuadFormCovFaithful S.fibre levels U B

/-- **The (3.156) mass `a⟨B,B⟩`**, at the level the source puts it: `B = Q_{ell₀}A`, so the mass is
the `S.fibre`-level coarse norm. (In the collapsed encoding this was forced to `0`; §5c shows it is
live in the corrected typing.) -/
noncomputable def massCorr (S : LevelSplit)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) : ℝ :=
  covCoarseBondInner (lineCoarseRestrictCovLM U S.fibre B) (lineCoarseRestrictCovLM U S.fibre B)

/-- **The corrected (3.157) sandwich `⟨B̃, C*Δ_kC B̃⟩`.** `C = fullC U S.constr Dinv` — the (3.157)
reparametrisation, which solves ONE equation per **`S.constr`**-coarse bond and therefore lands in
`ker Q_{ell₁}`; `Δ_k` is taken at **`S.fibre`**. The two block sides are different by construction
of `LevelSplit`; that single change is the whole repair. -/
noncomputable def cStarDeltaKCFormCorr (S : LevelSplit) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
    (Dinv : CoarseBond L S.constr → (SuTwo →ₗ[ℝ] SuTwo)) (Btil : Bond L → SuTwo) : ℝ :=
  deltaKCorr S levels U (fullC U S.constr Dinv Btil)

/-! ## §3 — the general non-degeneracy criterion (duality), `LevelSplit`-free

`Δ_k(B) = ‖D_U H B‖²` with `H B = B + (correction ∈ V)`. Any `u` orthogonal to `D_U(V)` therefore
sees `D_U H B` and `D_U B` identically; if it sees `D_U B` nontrivially, `D_U H B ≠ 0`, so
`Δ_k(B) > 0`. Cheap, exact, and it is the shape of EVERY non-degeneracy argument for this object:
`u ⊥ D_U(V)` is the finite-dimensional form of Bałaban's `D_U^* u ∈ range Q^*`. -/

/-- Positive-definiteness of the plaquette `L²` form, assembled from `hsInner`'s definiteness. -/
theorem covPlaqInner_self_pos_of_ne {X : PeriodicLatticePlaquette L → SuTwo} (hX : X ≠ 0) :
    0 < covPlaqInner X X := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hX
  have hppos : 0 < hsInner (X p) (X p) := by
    rcases lt_or_eq_of_le (hsInner_self_nonneg (X p)) with h | h
    · exact h
    · exact absurd (hsInner_self_eq_zero h.symm) hp
  unfold covPlaqInner
  exact Finset.sum_pos' (fun q _ => hsInner_self_nonneg (X q)) ⟨p, Finset.mem_univ p, hppos⟩

/-- `⟪u, 0⟫ = 0`, from additivity alone (no `hsInner` simp set needed). -/
theorem covPlaqInner_zero_right (u : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner u (0 : PeriodicLatticePlaquette L → SuTwo) = 0 := by
  have h := covPlaqInner_add_right u (0 : PeriodicLatticePlaquette L → SuTwo) 0
  rw [add_zero] at h
  linarith

/-- **THE DUALITY CRITERION.** If a plaquette field `u` annihilates `D_U(V)` — `V` the (3.156)
constraint subspace at the FIBRE level `ell` — and does not annihilate `D_U B`, then the Schur
complement at `B` is strictly positive. General in `ell`, `levels`, `U`, `B`. -/
theorem deltaJQuadFormCovFaithful_pos_of_dual_witness (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (u : PeriodicLatticePlaquette L → SuTwo)
    (hu : ∀ v ∈ gaugeConstraintSubspaceCovFaithful ell levels U,
      covPlaqInner u (curlCovariantLM U v) = 0)
    (hne : covPlaqInner u (curlCovariantLM U B) ≠ 0) :
    0 < deltaJQuadFormCovFaithful ell levels U B := by
  have hsplit : curlCovariantLM U (hjExtensionCovFaithful ell levels U B)
      = curlCovariantLM U B + curlCovariantLM U (hjCorrectionCovFaithful ell levels U B) := by
    show curlCovariantLM U (B + hjCorrectionCovFaithful ell levels U B) = _
    exact map_add _ _ _
  have hsees : covPlaqInner u (curlCovariantLM U (hjExtensionCovFaithful ell levels U B))
      = covPlaqInner u (curlCovariantLM U B) := by
    rw [hsplit, covPlaqInner_add_right,
      hu _ (hjCorrectionCovFaithful_mem ell levels U B), add_zero]
  have hXne : curlCovariantLM U (hjExtensionCovFaithful ell levels U B) ≠ 0 := by
    intro h0
    rw [h0, covPlaqInner_zero_right] at hsees
    exact hne hsees.symm
  exact covPlaqInner_self_pos_of_ne hXne

/-- The same criterion, stated on the corrected object. -/
theorem deltaKCorr_pos_of_dual_witness (S : LevelSplit) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (u : PeriodicLatticePlaquette L → SuTwo)
    (hu : ∀ v ∈ gaugeConstraintSubspaceCovFaithful S.fibre levels U,
      covPlaqInner u (curlCovariantLM U v) = 0)
    (hne : covPlaqInner u (curlCovariantLM U B) ≠ 0) :
    0 < deltaKCorr S levels U B :=
  deltaJQuadFormCovFaithful_pos_of_dual_witness S.fibre levels U B u hu hne

#print axioms covPlaqInner_self_pos_of_ne
#print axioms covPlaqInner_zero_right
#print axioms deltaJQuadFormCovFaithful_pos_of_dual_witness
#print axioms deltaKCorr_pos_of_dual_witness

/-! ### §3b — the criterion is SHARP, not merely sufficient

There is a CANONICAL `u`: the correction target `D_UB − P_W(D_UB)`, which lies in `Wᗮ` by
construction, so it satisfies the criterion's first hypothesis for free; and it pairs with `D_UB` to
give EXACTLY `Δ_k(B)`. Hence the criterion fires **iff** `Δ_k(B) > 0`. Two consequences worth
stating: (i) §3 loses nothing — any failure to exhibit a `u` is a genuine failure to prove
positivity, not an artefact of the method; (ii) §6's `[STOKES-COMM]` is therefore the right target
and not a detour, because a `u` is exactly what a proof must produce. -/

/-- The canonical `u` annihilates `D_U(V)` for free. -/
theorem canonical_dual_witness_annihilates (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    ∀ v ∈ gaugeConstraintSubspaceCovFaithful ell levels U,
      covPlaqInner (hjCorrectionTargetCovFaithful ell levels U B) (curlCovariantLM U v) = 0 := by
  intro v hv
  rw [covPlaqInner_symm]
  exact hjCorrectionTargetCovFaithful_orthogonal ell levels U B
    (curl_mem_curlImageCovFaithful_of_mem hv)

/-- …and its pairing with `D_UB` is exactly `Δ_k(B)`. -/
theorem canonical_dual_witness_pairing (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    covPlaqInner (hjCorrectionTargetCovFaithful ell levels U B) (curlCovariantLM U B)
      = deltaJQuadFormCovFaithful ell levels U B := by
  have horth : covPlaqInner (hjCorrectionTargetCovFaithful ell levels U B)
      (curlImageCovProjFaithful ell levels U (curlCovariantLM U B)) = 0 := by
    rw [covPlaqInner_symm]
    exact hjCorrectionTargetCovFaithful_orthogonal ell levels U B
      (curlImageCovProjFaithful_mem ell levels U _)
  have hdecomp : curlCovariantLM U B
      = hjCorrectionTargetCovFaithful ell levels U B
        + curlImageCovProjFaithful ell levels U (curlCovariantLM U B) := by
    unfold hjCorrectionTargetCovFaithful
    abel
  have hdelta : deltaJQuadFormCovFaithful ell levels U B
      = covPlaqInner (hjCorrectionTargetCovFaithful ell levels U B)
          (hjCorrectionTargetCovFaithful ell levels U B) := by
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful]
  rw [hdelta]
  conv_lhs => rw [hdecomp]
  rw [covPlaqInner_add_right, horth, add_zero]

/-- **SHARPNESS.** `Δ_k(B) > 0` **iff** the canonical dual witness sees `D_UB`. -/
theorem dual_witness_criterion_sharp (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    0 < deltaJQuadFormCovFaithful ell levels U B ↔
      covPlaqInner (hjCorrectionTargetCovFaithful ell levels U B) (curlCovariantLM U B) ≠ 0 := by
  rw [canonical_dual_witness_pairing]
  constructor
  · exact fun h => ne_of_gt h
  · intro h
    rcases lt_or_eq_of_le (deltaJQuadFormCovFaithful_nonneg ell levels U B) with h' | h'
    · exact h'
    · exact absurd h'.symm h

#print axioms canonical_dual_witness_annihilates
#print axioms canonical_dual_witness_pairing
#print axioms dual_witness_criterion_sharp

/-! ### §3c — the criterion in FACTORISED form: the exact obligation `[STOKES-COMM]` must meet

The first hypothesis of §3 (`u ⊥ D_U(V)`) is awkward to verify directly because `V` is large. It is
implied by a much more checkable statement: that the functional `v ↦ ⟪u, D_U v⟫` **factors through
the fibre map `Q_{ell}`**. That is exactly Bałaban's `D_U^*u ∈ range Q^*`, and it is exactly what the
flat Stokes identity of §6 supplies (with `u` the block-average of a coarse plaquette and `φ` the
evaluation of the coarse curl there). So the general-`k` non-degeneracy is reduced, in the kernel, to
producing ONE pair `(u, φ)` — no analysis, no constants, purely combinatorial. -/

/-- **THE REDUCTION.** If `⟪u, D_U ·⟫` factors through `Q_{ell}` via a linear `φ`, and `φ` does not
kill `Q_{ell}B`, then `Δ_k(B) > 0` — at ANY fibre level `ell`, any `levels`, any `U`. -/
theorem deltaJQuadFormCovFaithful_pos_of_factoring_witness (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (u : PeriodicLatticePlaquette L → SuTwo)
    (φ : (CoarseBond L ell → SuTwo) →ₗ[ℝ] ℝ)
    (hfac : ∀ v : Bond L → SuTwo,
      covPlaqInner u (curlCovariantLM U v) = φ (lineCoarseRestrictCovLM U ell v))
    (hne : φ (lineCoarseRestrictCovLM U ell B) ≠ 0) :
    0 < deltaJQuadFormCovFaithful ell levels U B := by
  refine deltaJQuadFormCovFaithful_pos_of_dual_witness ell levels U B u ?_ ?_
  · intro v hv
    rw [hfac v, (mem_gaugeConstraintSubspaceCovFaithful.mp hv).1, map_zero]
  · rw [hfac B]; exact hne

/-- The same, on the corrected object. -/
theorem deltaKCorr_pos_of_factoring_witness (S : LevelSplit)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (u : PeriodicLatticePlaquette L → SuTwo)
    (φ : (CoarseBond L S.fibre → SuTwo) →ₗ[ℝ] ℝ)
    (hfac : ∀ v : Bond L → SuTwo,
      covPlaqInner u (curlCovariantLM U v) = φ (lineCoarseRestrictCovLM U S.fibre v))
    (hne : φ (lineCoarseRestrictCovLM U S.fibre B) ≠ 0) :
    0 < deltaKCorr S levels U B :=
  deltaJQuadFormCovFaithful_pos_of_factoring_witness S.fibre levels U B u φ hfac hne

#print axioms deltaJQuadFormCovFaithful_pos_of_factoring_witness
#print axioms deltaKCorr_pos_of_factoring_witness

/-! ## §4 — `splitK0`: the `k = 0` member, `ell₀ = 1 < 2 = ell₁`

Bałaban's `Q_j(U) = Q(Ū^{j-1})·····Q(U)` is the `j`-fold composite, so `Q_0` is the EMPTY
composite — the identity, block side `1`. At `k = 0` the unit lattice IS the fine lattice, the
Schur fibre is a single point (`lineCoarseRestrictCovLM_one_eq_zero_imp`: `Q_1(U)` is injective,
`gaugeConstraintSubspaceCovFaithful_ell1_eq_bot`: `V = ⊥`), and `Δ_k` is the raw curl energy. `Q₁`
is still a genuine coarse-graining, here at `L = 2`. This is precisely the configuration of CMP96
Lemma 2.4 — the U=1 result CMP99b p.428 cites for `γ₀` — which mentions only `Q₁` and `∂₁` and has
no fine lattice in it at all. -/

/-- `(ell₀, ell₁) = (1, 2)`. -/
def splitK0 : LevelSplit := ⟨1, 2, Nat.one_pos, one_dvd 2, Nat.one_lt_two⟩

theorem splitK0_fibre : splitK0.fibre = 1 := rfl
theorem splitK0_constr : splitK0.constr = 2 := rfl

/-- **At `k = 0` the corrected `Δ_k` is EXACTLY the `D_U^*D_U` form** — no residual Schur
correction, because the fibre is trivial.

**Consequence for the standing residual `[CSTAR-SCHUR-GAP]`** (`CStarDeltaKCCoercive` §4:
`deltaJQuadFormCovFaithful ≤ dstarDQuadForm`, the direction that blocks transferring a lower bound
from the raw form to the Schur complement): at `ell₀ = 1` that inequality is an **equality**, so the
gap is VACUOUS here and §3's lower bound transfers verbatim. `[CSTAR-SCHUR-GAP]` opens only at
`ell₀ ≥ 2`, i.e. it is a `k ≥ 1` phenomenon, not a defect of the re-typing. -/
theorem deltaKCorr_splitK0_eq_dstarD (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    deltaKCorr splitK0 levels U B = dstarDQuadForm U B :=
  deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm levels U B

#print axioms splitK0_fibre
#print axioms splitK0_constr
#print axioms deltaKCorr_splitK0_eq_dstarD

/-! ## §5 — THE NON-DEGENERACY WITNESS

Everything below is on the compatible torus `witL5` (`L μ = 5`, so `4 ≤ L μ` and `2 ∣ L μ + 1`),
at `U = 1`, with `B := fullC U 2 (dinvC U 2) witA` — the (3.157) `C` applied to the axial-gauge,
dropped-bond-free field `witA`. -/

private noncomputable abbrev wU : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    RegularUDomainWitness.witL5 := trivialU RegularUDomainWitness.witL5

private noncomputable abbrev wB : Bond RegularUDomainWitness.witL5 → SuTwo :=
  fullC wU 2 (dinvC wU 2) RegularUDomainWitness.witA

/-- **THE DELIVERABLE.** In the CORRECTED typing (`ell₀ = 1`, `ell₁ = 2`), the explicit field `wB`

* lies in the (3.157) constraint subspace `ker Q₁ = ker (lineCoarseRestrictCovLM U 2)`;
* is nonzero (indeed has strictly positive bond energy);
* has **strictly positive** `Δ_k`, bounded below by the explicit `γ₀ · bondEnergy witA` with
  `γ₀ = (1/108)(1/2⁴)` and `0 < bondEnergy witA`.

No existential quantifier over free data appears (S91): every object is named. This is the property
`cStarDeltaKC_coercivity_refuted` proves the COLLAPSED encoding cannot have. -/
theorem corrected_nondegeneracy :
    lineCoarseRestrictCovLM wU 2 wB = 0
  ∧ wB ≠ 0
  ∧ 0 < bondEnergy RegularUDomainWitness.witA
  ∧ (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) * bondEnergy RegularUDomainWitness.witA
      ≤ deltaKCorr splitK0 (oneLevelUniv RegularUDomainWitness.witL5) wU wB
  ∧ 0 < deltaKCorr splitK0 (oneLevelUniv RegularUDomainWitness.witL5) wU wB := by
  obtain ⟨-, -, hE, hne⟩ := regularU_domain_nonvacuous_generalU wU
  have hker : lineCoarseRestrictCovLM wU 2 wB = 0 :=
    lineCoarseRestrictCovLM_fullC (by norm_num) RegularUDomainWitness.witL5_two_dvd wU
      (dinvC wU 2) (dinvC_hinv (by norm_num) RegularUDomainWitness.witL5_two_dvd wU)
      RegularUDomainWitness.witA
  obtain ⟨hcoer, hpos⟩ := cStarDstarDC_coercive_at_witA (0 : ℝ)
  have hform : cStarDstarDCForm 0 2 wU (dinvC wU 2) RegularUDomainWitness.witA
      = dstarDQuadForm wU wB :=
    cStarDstarDCForm_eq_dstarD 0 (by norm_num) RegularUDomainWitness.witL5_two_dvd wU
      (dinvC wU 2) (dinvC_hinv (by norm_num) RegularUDomainWitness.witL5_two_dvd wU)
      RegularUDomainWitness.witA
  have hred : deltaKCorr splitK0 (oneLevelUniv RegularUDomainWitness.witL5) wU wB
      = dstarDQuadForm wU wB :=
    deltaKCorr_splitK0_eq_dstarD (oneLevelUniv RegularUDomainWitness.witL5) wU wB
  have hbound : (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) * bondEnergy RegularUDomainWitness.witA
      ≤ deltaKCorr splitK0 (oneLevelUniv RegularUDomainWitness.witL5) wU wB := by
    rw [hred, ← hform]; exact hcoer
  refine ⟨hker, hne, hpos, hbound, ?_⟩
  have hγ : (0 : ℝ) < (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by norm_num
  exact lt_of_lt_of_le (mul_pos hγ hpos) hbound

#print axioms corrected_nondegeneracy

/-! ### §5b — THE SEPARATION: same field, same background, two levels -/

/-- At the COLLAPSED level (`ell₀ = ell₁ = 2`) the very same field gives `0`. Re-derived here from
`fullC_mem_V_of_R` + `deltaJQuadFormCovFaithful_eq_zero_of_mem_V`, not cited. -/
theorem collapsed_deltaK_eq_zero :
    deltaJQuadFormCovFaithful 2 (oneLevelUniv RegularUDomainWitness.witL5) wU wB = 0 := by
  have hR : RcovLM wU (oneLevelUniv RegularUDomainWitness.witL5)
      (gradCovariantAdjointLM wU wB) = 0 :=
    RcovLM_oneLevelUniv_eq_zero wU _
  exact deltaJQuadFormCovFaithful_eq_zero_of_mem_V 2
    (oneLevelUniv RegularUDomainWitness.witL5) wU wB
    (fullC_mem_V_of_R (by norm_num) RegularUDomainWitness.witL5_two_dvd
      (oneLevelUniv RegularUDomainWitness.witL5) wU (dinvC wU 2)
      (dinvC_hinv (by norm_num) RegularUDomainWitness.witL5_two_dvd wU)
      RegularUDomainWitness.witA hR)

/-- **THE ONE-PARAMETER MUTATION.** Everything is held fixed — the background `wU`, the level list,
the field `wB` — and only the FIBRE block side is moved from `2` (collapsed, equal to the
constraint side) to `1` (corrected, strictly below it). The value moves from identically `0` to
strictly positive. This is the defect and its repair, isolated. -/
theorem level_split_separates :
    deltaJQuadFormCovFaithful 2 (oneLevelUniv RegularUDomainWitness.witL5) wU wB = 0
  ∧ 0 < deltaJQuadFormCovFaithful 1 (oneLevelUniv RegularUDomainWitness.witL5) wU wB := by
  refine ⟨collapsed_deltaK_eq_zero, ?_⟩
  obtain ⟨-, -, -, -, hpos⟩ := corrected_nondegeneracy
  exact hpos

#print axioms collapsed_deltaK_eq_zero
#print axioms level_split_separates

/-! ### §5c — the (3.156) MASS is revived by the same re-typing

In the collapsed encoding `Q₁(C B̃) = 0` forced the mass `a⟨B,B⟩` to vanish identically, which is
why `cStarDstarDCForm` was proved `a`-free. At the corrected fibre level `ell₀ = 1` the map is
injective, so the mass is strictly positive on the same field. (Per the source the `a`-term is
cancelled by `Q*aQ` inside `Δ + Δ⁽²⁾`; the point here is only that the collapsed encoding could not
even SEE the term.) -/

theorem massCorr_splitK0_pos : 0 < massCorr splitK0 wU wB := by
  have hQne : lineCoarseRestrictCovLM wU 1 wB ≠ 0 := by
    intro h
    exact (regularU_domain_nonvacuous_generalU wU).2.2.2
      (lineCoarseRestrictCovLM_one_eq_zero_imp wU h)
  exact covCoarseBondInner_pos_of_ne hQne

/-- The collapsed counterpart: at block side `2` the same mass is `0`. -/
theorem mass_collapsed_eq_zero :
    covCoarseBondInner (lineCoarseRestrictCovLM wU 2 wB) (lineCoarseRestrictCovLM wU 2 wB) = 0 := by
  obtain ⟨hker, -⟩ := corrected_nondegeneracy
  rw [hker]
  exact covCoarseBondInner_zero

#print axioms massCorr_splitK0_pos
#print axioms mass_collapsed_eq_zero

/-! ## §6 — WHAT IS NOT PROVED, AND THE EXACT MISSING LEMMA

**⚠ SUPERSEDED IN PART, 2026-07-27 (S75, propagated by the main loop — the closing lane could not edit
this file). Read this header before the section below; three of its claims are no longer true at
`U = 1`.**

| §6 claim as written | status now | closing declaration |
|---|---|---|
| `[STOKES-COMM]` "not closed" | **CLOSED at `U = 1`, general `ell`** | `ThirdLevelStokes.stokes_flat`, `stokes_factoring` — the exact identity `∂₁′ ∘ Q_ell = P_ell ∘ d`, every `ell > 0`, every compatible torus, every coarse plaquette |
| witness at `ell₀ ≥ 2` "not established" | **ESTABLISHED at `U = 1`** | `ThirdLevelWitness.third_level_nondegeneracy` — torus `L = 7`, split `(2,4)`: `Q₄B7 = 0`, `B7 ≠ 0`, fibre `V(2) ≠ ⊥` with a NAMED member, and `0 < deltaKCorr`. Quantitative, not just a sign: `(1/64)·bondEnergy B7 ≤ deltaKCorr` |
| `[Q-SEMIGROUP]` "not proved" | **PROVED at `U = 1`** as a full 3-D operator identity (§7 had only the 1-D `decide` core) | `ThirdLevelArrows.tower_law` (needs only `ell₀ ∣ L μ + 1`, not `ell₁`), plus `ker_translation`: `v ∈ ker Q_{ell₁} ↔ Q_{ell₀} v ∈ ker Q₁` — the translation §6 said the corrected typing owed |

**What is NOT superseded, and is the honest remaining frontier.** All three closures are at `U = 1`.
The covariant statements stay open, and their resistance point is now measured rather than named:
`[STOKES-COMM-U]`'s numerator half is closed for EVERY `U`
(`ThirdLevelSchurGap.general_U_pairing_control`), while the denominator needs turning an
`O(α₁·√E(v))` error into `O(α₁·‖D_U v‖)` on the fibre — a reverse Poincaré on `V_U`, which is itself a
coercivity statement, so the route is NEAR-CIRCULAR as it stands. Bałaban breaks that circle with the
`U = 1` base plus `Mα₀` analyticity (GOAL_LEMMA §4 (b1)–(b3)), not by proving the reverse inequality
directly.

**[S75 CORRECTED 2026-07-28, then CORRECTED AGAIN THE SAME NIGHT — read the second one.]**
This paragraph originally read: *"`[Q-TRANSPORT-COMPOSE]` (the covariant tower law) is open with
the same curvature obstruction, `witness_curvature_ne_zero`."*

The first correction replaced that with "the exact operator identity is FALSE", citing
`Balaban.TowerLawCovariant.tower_law_cov_refuted`. **That went too far, and the main loop wrote
it — this is a self-correction, not a gate's.** A second-family prosecution then convicted the
refutation on OBJECT IDENTITY: CMP99b p.393 (3.15) defines `Q_j(U)` as the COMPOSITION of one-step
operators, with CMP98 pp.29-30's higher-order contour built RECURSIVELY through block corners —
not as a fresh one-shot staircase at the large scale, which is what the refutation's right-hand
side uses. The prosecution's own compiled "the tower law then HOLDS" theorem is a TAUTOLOGY
(`LHS = LHS`; its transport is byte-identical to the refutation's `lhsTransport`), so it does not
establish the converse either.

**SETTLED, later the same night — third-family source adjudication (Kimi, blind).** CMP99b p.393
(3.15) DEFINES `Q_j(U)` as the composition, with no proof verb; the only one-shot large-block
formula on those pages is (3.19), which applies to the PRIMED operator alone and whose kernel is
itself defined by the same corner-by-corner product. **There is no independently-defined one-shot
object in the source, so the tower law is a DEFINITION and cannot be refuted.**
`tower_law_cov_refuted` is correct mathematics about an identity WE constructed.

**Consequence for this section, and it is a redirection not a closure:** coercivity cannot be
transferred across scales via an identity, because the coarse operator IS the composite by
definition. The bound must be proved for the composite DIRECTLY — so the `k`-uniformity of
`tower_law_cov_error_alpha` described above is the live question, not a fallback. One residual
stays open (O1): CMP98 (52),(53), the primary definition both (3.19) and (3.55) defer to, was not
in the evidence set; if it defines `Γ^(j)` geometrically rather than recursively, the PRIMED
operator's status softens to a deferred assertion. The unprimed ruling is unaffected. See `Balaban/TowerLawCovariant.lean` §9 for the full account, including which
of the refutation's machinery survives — its MECHANISM (`contourSplit_fails`) does, since the
live question becomes whether the recursive composite equals the direct block average, and for
curved `U` it does not.

The surviving target is the error-carrying form `tower_law_cov_error_alpha`,
`‖LHS − RHS‖ ≤ N·2α₁·Kv`, exact at `α₁ = 0`, **not proved `k`-uniform** — and `k`-uniformity is
precisely what this section needs, since for `V = Ū` each unit link is a product of `ℓ₀` fine links
(`α₁^unit ~ ℓ₀·α₁^fine`) while `N` grows with the in-block staircase length. Whether the
accumulated defect can stay below `γ₀` across RG steps is the open question, and it is now a
QUANTITATIVE one rather than a yes/no one. Also live: the refutation's mechanism is stated over a
contour family whose fidelity to CMP109 p.252's signed prescription is CANNOT-DETERMINE (see
`BlockedGaugeCore.contourSteps`); a prosecution is running on whether a source-faithful family
restores additivity.

The original text is kept below unedited, because the reduction it performs (§3 → §3c) is what the
closing lane executed, and a struck section that still teaches its own route is worth more than a
deleted one.

**`[STOKES-COMM]` — the one named residual this module creates and does not close.**
~~(as of this section's writing; see the superseded table above)~~

For `ell₀ ≥ 2` the Schur fibre `V = ker Q_{ell₀} ∩ ker R` is nontrivial and §5's route is
unavailable (it used `V = ⊥`). §3 reduces non-degeneracy at any `ell₀` to producing a plaquette
field `u` with

  `covPlaqInner u (curlCovariantLM U v) = 0` for all `v ∈ V`,  and
  `covPlaqInner u (curlCovariantLM U B) ≠ 0`.

§3c reduces this further, in the kernel, to a strictly cheaper obligation
(`deltaKCorr_pos_of_factoring_witness`): produce a pair `(u, φ)` with `φ` linear and

  `covPlaqInner u (curlCovariantLM U v) = φ (lineCoarseRestrictCovLM U ell v)`  for ALL `v`,

i.e. make `⟪u, D_U ·⟫` **factor through `Q_{ell}`** (Bałaban's `D_U^*u ∈ range Q^*`). Then the
orthogonality to `D_U(V)` is automatic and only `φ(Q_{ell}B) ≠ 0` remains. There is no analysis and
no constant left in the obligation; it is purely combinatorial.

The source supplies exactly such a pair, and it is the flat Stokes identity behind CMP96 (2.128)'s
`Σ_p |(∂₁B)(p)|²` term: the coarse curl of a block-averaged line integral is a block-average of fine
curls,

  `(∂₁'(Q_{ell}A))(y,μ,ν) = (1/ell⁴) Σ_{x ∈ B(y)} Σ_{i<ell} Σ_{j<ell} (dA)(x + i e_μ + j e_ν, μ, ν)`,

i.e. `∂₁' ∘ Q_{ell} = P_{ell} ∘ d` for the plaquette block-average `P_{ell}`. Given it, take
`φ := ⟪δ_{P'}, ∂₁' ·⟫` and `u := P_{ell}^* δ_{P'}`; the factorisation hypothesis of §3c is exactly
the displayed identity, and `φ(Q_{ell}B) ≠ 0` says the coarse curl of `Q_{ell}B` is nonzero at `P'`.
**This is the whole content of the general-`k` case.**

*The proof of the identity, written out so the next lane does not re-derive it.* Two telescopings.
Write `Λ_μ(x) := Σ_{i<ell} A(x+i e_μ, μ)` (the length-`ell` line integral) and
`(dA)(z,μ,ν) = A(z,μ) + A(z+e_μ,ν) − A(z+e_ν,μ) − A(z,ν)`. Then

  `Σ_{i<ell} (dA)(x+i e_μ+j e_ν, μ,ν)`
    `= Λ_μ(x+j e_ν) − Λ_μ(x+(j+1)e_ν) + A(x+ell·e_μ+j e_ν, ν) − A(x+j e_ν, ν)`

(the `μ`-terms assemble into two line integrals, the `ν`-terms telescope in `i`), and summing over
`j < ell` telescopes again to

  `Λ_μ(x) − Λ_μ(x+ell·e_ν) + Λ_ν(x+ell·e_μ) − Λ_ν(x)`,

the holonomy of `A` around the `ell × ell` loop at `x`. Averaging over `x ∈ B(y)` and using
`coarseShift_blockOf_eq_image` (already in `CoarseShiftCovariance`) to identify
`B(coarseShift y ell μ) = B(y) + ell·e_μ` gives the four terms of `∂₁'(Q_{ell}A)(y,μ,ν)`.

*Two further obligations the flat identity alone does NOT discharge, stated so they are not
discovered late.* (i) The identity above is FLAT and real-valued; §3c is `SuTwo`-valued and
covariant. At `U = 1` the bridge is the componentwise reduction of `curlCovariantLM` to `curlValue`
(`CovU1Reduction` / `SuTwoGeomU1`); for `U ≠ 1` the transport does not cancel around the loop and the
identity acquires a curvature defect — `CovariantOperators.witness_curvature_ne_zero` is the
obstruction, and the honest general-`U` statement is the identity up to an `O(α₁)` remainder, which
is Bałaban's own "localizing the operators in `Δ_k`" step on p.428. (ii) `‖u‖` enters no statement
in §3/§3c (they are strict-positivity statements only); a UNIFORM `γ₀` would need `‖u‖` controlled
independently of `k`, which is a different and strictly harder obligation.

*Evidence of resistance (OPS-1), not a bare label.* Four routes were attempted before naming it.
(a) Direct duality with `u` a single fine plaquette: fails — `Q_{ell}^*ψ` must be orthogonal to
`ker d`, and `ker d` contains all gradients, so `ψ` must annihilate coarse gradients, forcing
`ψ = ∂₁'^*(·)`, i.e. forcing the Stokes identity.
(b) Attainment/compactness (`inf = 0 ⇒ attained ⇒ B ∈ Q(ker d)`): gives the right criterion but no
explicit constant and still needs `Q(ker d) ≠` everything, which is again the Stokes identity
(`coarseCurlValue_coarseGradient` alone is not enough: it handles `Q ∘ grad`, not `Q ∘ (ker d)`).
(c) Transfer of `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`: its hypothesis is
`A ∈ ker Q_{ell}`, but the corrected `B` lies in `ker Q_{ell₁}` with `ell₁ > ell₀`, and
`ker Q_{ell₀} ⊆ ker Q_{ell₁}` is the WRONG inclusion for the transfer.
(d) Injectivity of `curlCovariantLM U` at a curved background (which would make `Δ_k(B) > 0 ⇔ B ∉ V`
outright): true-looking but it is a rank statement on a 375-dimensional space at `witL5`, not
reachable by hand and not by `decide` over `ℝ`.
The tree does NOT contain `[STOKES-COMM]`: `LineIntegralAveraging` proves the GRADIENT intertwining
(`lineCoarseRestrict_gradValue`, `coarseCurlValue_lineCoarseRestrict_gradValue`) and `CoarseCurl`
proves the corresponding statement FAILS for the plain (non-line-integral) block average
`coarseRestrict` — neither is the identity above.

**`[Q-SEMIGROUP]` — a second residual, DISCLOSED because it is the weak point of the
identification, not because a gate found it.**

This tree presents every level pulled back to the fine bond space, and indexes the tower by block
side. The identification in the table above therefore reads `Q₁ ∘ Q_{ell₀} = Q_{ell₀·m}` — Bałaban's
`Q_j(U) = Q(Ū^{j-1})·····Q(U)`, the composite of one-step averagings. ~~That semigroup property is
**asserted by Bałaban's definition but is NOT proved in this tree**~~: `lineCoarseRestrictCov U ell` is
defined directly at block side `ell`, never as a composite. Precisely what it buys is the
translation `A ∈ ker Q_{ell₁} ⟺ Q_{ell₀}A ∈ ker Q₁`, i.e. that the pulled-back constraint really is
"the unit field `B = Q_{ell₀}A` lies in `ker Q₁`" as (3.156) demands.

**STRUCK 2026-07-30 — STALE, AND CONTRADICTED BY THIS FILE'S OWN TABLE ~130 LINES ABOVE.** The
superseded-header table in §5 already records `[Q-SEMIGROUP]` as **PROVED at `U = 1`**, and it is:
`ThirdLevelArrows.tower_law` gives the full 3-D operator identity (needing only `ell₀ ∣ L μ + 1`, not
`ell₁`), and `ThirdLevelArrows.ker_translation` gives exactly the translation this paragraph says the
corrected typing owed — `v ∈ ker Q_{ell₁} ↔ Q_{ell₀} v ∈ ker Q₁`. Both are cited by NAME here rather
than by line, because a line citation elsewhere in this tree went stale within four minutes.

**What is NOT closed, and the strike does not touch:** general covariant `U`. `TowerLawCovariant`'s own
closing note is deliberately two-sided and must not be rounded off in either direction — *"not 'the
tower law is false' (the object is in doubt), and not 'the tower law holds' (the only artifact offering
that is a tautology)"* — with `tower_law_cov_error_alpha` the surviving target, still not proved
uniform. So the correct reading is: **closed at `U = 1`, open at general `U`, and open in both
directions there.**

**Cost of this one stale sentence, recorded because it is the point.** It sent the `KerQDescent` lane
down a ~170-line from-scratch rebuild of a kernel inclusion that closes in four lines via `tower_law`.
Its own nested validator caught the duplication. The lane then kept BOTH proofs rather than deleting
the redundant one — `KerQDescent.kerQ2_subset_kerQ4_via_tower` proves the same `Prop` by the other
route, sharing no lemma — so their agreement is de-correlated evidence *for* `tower_law`, which that
lane consumes and never prosecuted. Retaining the duplicate was the right call.

Scope of the damage, stated exactly:

* **No theorem in this module uses it.** Every proof above is about `deltaJQuadFormCovFaithful ell₀`
  and `fullC U ell₁` directly; the mathematical content — `Δ_k` does not vanish on a constraint
  subspace cut at a STRICTLY COARSER level — stands without it.
* **At `splitK0` it is discharged, trivially.** With `ell₀ = 1`, `Q_1(U)` is the bond-wise
  invertible transport `A ↦ R(g)·A(y,μ)` (`lineCoarseRestrictCovLM_one_eq_zero_imp`), and at the
  witness's `U = 1` it is literally the identity `Bond L ≅ CoarseBond L 1`. So `Q₁ = Q_{ell₁}` on the
  nose and no composition law is needed: §5's witness IS Bałaban's `k = 0` typing, not an analogue.
* **For `ell₀ ≥ 2` it is a genuine obligation**, and it must be discharged BEFORE the table above may
  be quoted at those levels. **§7 discharges its decidable core** — the flat along-μ weight identity
  `directCoeff (L*L) t = compositeCoeff L t` for `L = 2, 3` (`tower_coeff_L2`, `tower_coeff_L3`, by
  `decide`, with a discriminating control `tower_coeff_control`), plus the transverse index
  decomposition (`transverse_decompose`). What remains is `[Q-TRANSPORT-COMPOSE]`: that the covariant
  transports compose around the two-step path, the same curvature question as `[STOKES-COMM]`(i).
  So the tower law is **not false for combinatorial reasons**, which is exactly what a
  block-side-indexed encoding needed and did not have.

**What each downstream module needs (reported, not edited — LAW-4/write-scope).**

* `CStarDeltaKCCompose` — its `cStarDeltaKCForm a ell levels U C B̃` uses ONE `ell` for the `Δ_k`
  fibre and for the `C` whose image is `ker Q_{ell}`. It needs a second block-side parameter: the
  `Δ_k` argument at `S.fibre`, the `C` at `S.constr`. Its §1–§4 content (generic real-linear `C`)
  survives verbatim; only the instantiation changes. Its header's "NOT (ii)" verdict — "the two
  `Q₁`'s are literally the same `LinearMap`" — is the defect and should be struck (S75).
* `CStarDeltaKCCoercive` — §3's `cStarDstarDC_coercive` is UNAFFECTED and is in fact the `ell₀ = 1`
  input to §5 above. §5b's `cStarDeltaKC_coercivity_refuted` remains true and should be re-labelled:
  it refutes the COLLAPSED object, and `collapsed_deltaK_eq_zero` here re-derives its mechanism.
  §4's `[CSTAR-SCHUR-GAP]` (`deltaJ ≤ dstarD`) is unaffected and still blocks a transfer at
  `ell₀ ≥ 2`.
* `FullReparamC` / `ReparamC*` — UNAFFECTED. `fullC U ell Dinv` is exactly the (3.157) `C` at block
  side `ell = S.constr`; `fullC_mem_kerQ` is exactly `Q₁(C B̃) = 0`. Nothing there was wrong.
* `DeltaKSuTwoAssembly` — `deltaKSuTwoForm`'s mass and fibre share a block side, which §2 above
  shows is CORRECT per (3.156) (`B = QA`). Only its composition with `C` needs the split.
-/

/-! ## §7 — `[Q-SEMIGROUP]`, the decidable core: CHECKED, not assumed

§1's table indexes the levels by BLOCK SIDE rather than by building a third lattice, and that move
relies on the tower law `Q_{L²} = Q^{coarse}_L ∘ Q_L`. Bałaban DEFINES `Q_j(U)` as the composite
(p.393 (3.15)), but CMP95 (1.18) also gives a DIRECT formula at block side `M`; the two must agree,
and nothing in this tree checked that they do. Here is the decidable core of the check.

For a bond field, the direct block-line average at side `M` gives the bond at μ-offset `t` the
integer weight `directCoeff M t = #{(s,j) ∈ [0,M)² : s + j = t}` (`s` = site inside the block, `j` =
step along the length-`M` line integral), under the overall normalisation `M^{-(d+1)}`. The
two-step composite at `L` with `M = L²` gives it `compositeCoeff L t = Σ_{u,v} c^L_u c^L_v [Lu+v=t]`,
under `(L^{-(d+1)})² = M^{-(d+1)}` — the SAME normalisation, so the whole content is the integer
identity `directCoeff (L*L) t = compositeCoeff L t`.

**Scope, exactly.** This is the FLAT, ABELIAN, ALONG-μ coefficient core plus the transverse index
bookkeeping. It does NOT by itself establish
`lineCoarseRestrictCov U (L*L) = Q^{coarse}_L ∘ lineCoarseRestrictCov U L`, which additionally needs
the covariant transports to compose around the two-step path — `[Q-TRANSPORT-COMPOSE]`, the same
curvature question as `[STOKES-COMM]`(i). What §7 does settle is that the tower law is not FALSE for
combinatorial reasons, which is what a block-side-indexed encoding needed and did not have. -/

/-- CMP95 (1.18)'s direct block-line weight at block side `M`, μ-offset `t` (integer part; the
`M^{-(d+1)}` normalisation is factored out). -/
def directCoeff (M t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range M, ∑ j ∈ Finset.range M, if s + j = t then 1 else 0

/-- The two-step composite weight at block side `L` (so total side `L*L`), μ-offset `t`. -/
def compositeCoeff (L t : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (2 * L - 1), ∑ v ∈ Finset.range (2 * L - 1),
    if L * u + v = t then directCoeff L u * directCoeff L v else 0

/-- **`L = 2`, `M = 4`** — the case the level split `splitK0`-successor `(2,4)` would use. The
profiles are `(1,2,3,4,3,2,1)` both ways. -/
theorem tower_coeff_L2 : ∀ t ∈ Finset.range 7, directCoeff 4 t = compositeCoeff 2 t := by decide

/-- **`L = 3`, `M = 9`** — a second, independent value of `L`, so the agreement is not an artefact
of `L = 2`. -/
theorem tower_coeff_L3 : ∀ t ∈ Finset.range 17, directCoeff 9 t = compositeCoeff 3 t := by decide

/-- **FALSIFIABILITY CONTROL.** The identity is not a tautology of the two definitions: mismatching
the sides breaks it. `directCoeff 4 3 = 4` but `compositeCoeff 3 3 = 4`… so a same-value collision is
possible pointwise; the honest control is a PROFILE mismatch — `directCoeff 9` and
`compositeCoeff 2` disagree at `t = 4` (`5 ≠ 3`), and `directCoeff 4` and `compositeCoeff 3` disagree
at `t = 5` (`2 ≠ 6`). So `decide` above is discriminating, not vacuous. -/
theorem tower_coeff_control :
    directCoeff 9 4 ≠ compositeCoeff 2 4 ∧ directCoeff 4 5 ≠ compositeCoeff 3 5 := by decide

/-- The transverse half of the bookkeeping: every offset `τ < L*L` decomposes UNIQUELY as
`L * a + s` with `a, s < L`, exhibited constructively (no existential over free data). -/
theorem transverse_decompose (L τ : ℕ) (hL : 0 < L) (hτ : τ < L * L) :
    L * (τ / L) + τ % L = τ ∧ τ / L < L ∧ τ % L < L := by
  refine ⟨Nat.div_add_mod τ L, ?_, Nat.mod_lt _ hL⟩
  exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hτ)

#print axioms directCoeff
#print axioms tower_coeff_L2
#print axioms tower_coeff_L3
#print axioms tower_coeff_control
#print axioms transverse_decompose

end AdalyFormal.Balaban.CStarLevelCorrected
