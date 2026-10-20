/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKSuTwoAssembly
import AdalyFormal.Balaban.ReparamCSuTwo

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[CSTAR-DELTAK-C-COMPOSE]` — the `C*Δ_kC` composition on su(2), concrete (3.157) `C` over the
(3.156) `Δ_k` form

## ⚠ INHERITED CORRECTION (2026-07-26) — `concreteWitnessC` IS PINNED TO THE WRONG DROPPED BOND

`ReparamCSuTwo.droppedBond` is **not** CMP99b p.428's `b₀` for `ell ≥ 2` (full statement + the three
named kernel refutations: the CORRECTION BANNER at the top of `Balaban/ReparamCSuTwo.lean`; the
derivation: `compute/cstar_roadmap/GAP2_DECOUPLING.md`). This module instantiates it in exactly ONE
place — `concreteWitnessC` (§5) — and therefore §5 is affected. **§1–§4 are NOT affected**: they
quantify over a generic real-linear `C` and never mention `droppedBond`.

**Corrected instantiation (STATED, NOT BUILT here).** `concreteWitnessC` should read

    reparamCSuTwo witnessU witnessEll targetCoarseBond
      (ReparamCDisjoint.droppedBondLast witnessEll targetCoarseBond) Dc_inv

with `Dc_inv` a right inverse of `coeffDc` **at that bond**. It is NOT `(witnessEll:ℝ)^4 • id`: at
offset `ell−1` the block-sum reaches `b₀` TWICE (at `ell = 2`) with transport `U_μ(y)` both times, so
`coeffDc = (1/ell⁴) • (2 • RMap (U_μ(y))) = (1/8) • RMap (U_μ(y))`, inverted by
`8 • RMap ((U_μ(y))⁻¹)` (invertibility by `RMap_mul` + `RMap_one`, no numerics).
The ingredients exist as named theorems in `ReparamCDisjoint` (`readers_ell2`, `transport_terms_eq`,
`gammaPath_shift`, the last carrying an extra side condition `0 < L μ`).
~~what is missing is the `coeffDc`-at-`droppedBondLast` assembly (the analogue of
`ReparamCSuTwo.coeffDc_witness`) and hence `hinv`.~~ **CORRECTED, same pass (retained struck): this
is NOT missing.** `Balaban/FullReparamC.lean` (a concurrent lane; uncommitted and in flight at the
time of this pass, `0` occurrences of `sorry`) already carries `coeffDc_ell2` /
`coeffDc_ell2_op` / `dinvEll2` / `dinvEll2_hinv` and, for GENERAL `ell`, `coeffDc_general` /
`coeffDc_general_op` / `dinvC` / `dinvC_hinv` (`coeffDc = (1/ell³)·RMap(dropTransport)`, inverted by
`ell³ • RMap(dropTransport⁻¹)`), plus the full-`C` result `fullC_mem_kerQ`. Note the general-`ell`
inverse is `ell³ • …`, NOT `(ell⁴/2) • …` — those coincide only at `ell = 2`. So the retarget of
`concreteWitnessC` is now pure plumbing (an import + an instantiation), not new mathematics; it is
left undone here only because of the write-scope/import considerations below.

**Why the retarget is not performed in this commit.** `Balaban/ReparamCDisjoint.lean` is another
lane's live write-scope and is not currently imported here; adding the import and rebuilding the
retargeted `C` inside this module would both change this module's dependency graph under a
concurrent lane and duplicate work that belongs upstream. So §5 is **annotated in place, retained
struck where its claims no longer hold** (S75), and the retarget is reported, not silently made.

**GRADE-2 CORRECTION (2026-07-26, `compute/sol_deltak_readjudicate/SOL_VERDICT.md`).** The (3.156)
`Δ_k` averaging mass CANCELS exactly against the leading Schur mass, so at `U=1`
`Δ_k = deltaJQuadFormCovFaithful` (pure minimized curl, DeltaKSuTwoAssembly `deltaK_at_U1_eq_deltaJ`).
Hence the FAITHFUL (3.157) sandwich at `U=1` is `⟨B̃, C*Δ_kC B̃⟩ = deltaJ(C B̃) = cStarDeltaKCForm 0`.
For `a≠0`, `cStarDeltaKCForm a = deltaJ(C B̃) − a‖Q₁(C B̃)‖²` carries a SPURIOUS extra mass (the
double-subtraction inherited from `deltaKSuTwoForm a`); it is NOT `⟨B̃, C*Δ_kC B̃⟩`. The whole `a≠0`
"mass-survival" analysis below is RETAINED as algebra but RE-READ under this correction (see the
VERDICT note).

**Culminating assembly brick of the su(2) `C*Δ_kC` object.** This module COMPOSES the two prior,
independently prosecuted bricks (LAW-19, read-only reuse):
* `DeltaKSuTwoAssembly.deltaKSuTwoForm a ell levels U A0` — the algebraic object
  `deltaJQuadFormCovFaithful A0 − a·⟨Q₁A0, Q₁A0⟩` (the faithful (3.156) `Δ_k` at `U=1` is the `a=0`
  slice), and
* `ReparamCSuTwo.reparamCSuTwo U ell c b₀ Dc_inv` — the CONCRETE (3.157) reparametrization `C`
  (identity off one dropped bond `b₀`, solving `(Q₁(U)(C B̃))(c)=0` there),

into `cStarDeltaKCForm a … (C B̃) = deltaKSuTwoForm a … (C B̃)`; the faithful `⟨B̃, C*Δ_kC B̃⟩` at
`U=1` is the `a=0` case `= deltaJ(C B̃)`.

## THE LOAD-BEARING QUESTION, RESOLVED (source-pinned)

CMP99b (3.157), adjudicated `corpus/pages/CMP99b_p428.md`:
`e^{½⟨g,C^{(k)}(Λ)g⟩} = (Z')⁻¹ ∫ dB̃ exp[−½⟨B̃, C*Δ_kC B̃⟩ + ⟨B̃, C*g⟩]`, so **`C*Δ_kC` acts on the
FREE-bond field `B̃`**, and `⟨B̃, C*Δ_kC B̃⟩ = ⟨CB̃, Δ_k(CB̃)⟩` is the substitution `B = C B̃` into
the (3.156) form `⟨B, Δ_k B⟩`. The dispatch's dichotomy:
* **(i)** genuine simplification — `C` lands in `ker Q₁`, mass term `−a⟨Q₁B,Q₁B⟩` identically `0` on
  `image C`, hence `C*Δ_kC = deltaJ∘C`; OR
* **(ii)** a type/scale confusion — the `Q₁` in `C`'s constraint is a DIFFERENT map than the `Q₁` of
  the mass term.

**VERDICT (RE-READ under the grade-2 correction) — it is NOT (ii).** In the faithful `Δ_k` (= `deltaJ`,
mass already cancelled) the sandwich is `deltaJ∘C` with NO mass, for ANY `C` — this is the `a=0`
form `cStarDeltaKCForm 0`. The `a≠0` "mass-survival" statements below concern the SPURIOUS extra
`−a‖Q₁(CB̃)‖²` of the mis-billed `deltaKSuTwoForm a`, not a mass in `Δ_k`. They remain algebraically
true and are kept for the record, but they do NOT describe `⟨B̃, C*Δ_kC B̃⟩` (which is `a=0`). The
NOT-(ii) pin (single `Q₁` LinearMap, no scale confusion) stands. The original text is retained below,
scoped to the spurious-mass object.

* ~~**NOT (ii) — the two `Q₁`'s are literally the same `LinearMap`.** In the Lean encoding there is
  exactly ONE covariant coarse-graining `Q₁ := lineCoarseRestrictCovLM U ell : (Bond L → SuTwo) →ₗ
  (CoarseBond L ell → SuTwo)`. `deltaKSuTwoForm`'s mass term is
  `a·covCoarseBondInner (Q₁ A0) (Q₁ A0) = a·∑_{c : CoarseBond L ell} ‖(Q₁ A0)(c)‖²`, and
  `reparamCSuTwo`'s proved constraint (`ReparamCSuTwo.reparamCSuTwo_constraint`) is
  `lineCoarseRestrictCov U ell (C B̃) c₀ = (Q₁(C B̃))(c₀) = 0` — the SAME `Q₁` evaluated at the single
  coarse bond `c₀`. No second map, no scale confusion.~~ `cStarDeltaKCForm_eq` makes this manifest.

  **⚠ SUPERSEDED FRAMING (S75, struck 2026-07-26).** The (i)/(ii) dichotomy above is a false
  dichotomy — `compute/q1_adjudication/RULING.md` (§4, §7 row 5) and this module's own sibling
  `CStarLevelCorrected.lean` (§"HOW TO SAY THIS CORRECTLY", self-flagging the identical point)
  settle it: `Q` and `Q₁` are the SAME one-step map template (`q_onestep_template_QV` in
  `compute/denotation_dict/DENOTATION_DICT.tsv`) instantiated at one `ell`, so within a SINGLE `ell`
  instantiation "the two `Q₁`'s are literally the same `LinearMap`" is correct as far as it goes —
  but the source's actual (3.156)/(3.157) needs the constraint (`Q₁`, unit→`Λ'`) and the mass/fibre
  (`Q`, fine→unit) at TWO DIFFERENT levels (`ell₀ ∣ ell₁`, `ell₁/ell₀ ≥ 2`), not the same `ell`. This
  module's `deltaKSuTwoForm`/`reparamCSuTwo` pairing above uses a SINGLE `ell` for both roles — the
  collapsed instantiation `CStarLevelCorrected.lean` was built to repair. So "no second map, no scale
  confusion" is true of the map (one template) but elided the real defect, which is a scale
  confusion in the INSTANTIATION (one `ell` doing two jobs), not in the map identity.

* **(i) holds when the coarse field is FULLY killed.** `cStarDeltaKCForm_eq_deltaJ_comp_of_coarse
  _field_zero`: if `Q₁(C B̃) = 0` as a FULL coarse field (all coarse bonds), the mass vanishes and
  `cStarDeltaKCForm = deltaJ∘C` — machine-checked. Balaban's FULL (3.157) `C` parametrizes exactly
  the subspace `{B : …, Q₁B=0}` (p.428 verbatim: "This form is considered on the subspace
  {B : …, Q₁B=0}. We can parametrize this subspace … B = C B̃"), so his full `C` DOES land in `ker Q₁`
  and there `C*Δ_kC = deltaJ∘C`. This is genuine simplification (i).

* **The concrete `C` here is SINGLE-CONSTRAINT ⇒ the mass is RETAINED.** `reparamCSuTwo` zeros only
  the `c₀`-summand (`c₀ = targetCoarseBond`): `(Q₁(C B̃))(c₀)=0`. The mass is a sum over ALL
  `CoarseBond witnessL 2` (`CoarseLattice witnessL 2` has 2³ = 8 sites, `× Fin 3` = 24 coarse bonds;
  `#eval …card = 24`), so killing ONE summand does not zero the field.
  By `cStarDeltaKCForm_massTerm_eq_zero_iff`
  (positive-definiteness) the mass vanishes IFF the whole field `Q₁(C B̃)=0`, which the single
  constraint does NOT force. **So for the single-constraint `C`, `cStarDeltaKCForm = deltaJ∘C − (mass
  term that is NOT identically zero)`; the mass survives, carried by the SAME `Q₁`.**

## What is built (all kernel-checked; `#print axioms` at each brick)

§1 `cStarDeltaKCForm a ell levels U C B̃ := deltaKSuTwoForm a … (C B̃)` — the (3.157) sandwich, over
a generic real-linear `C`, and `cStarDeltaKCForm_eq` pinning it to `deltaJ∘C − a·⟨Q₁(CB̃),Q₁(CB̃)⟩`
with the SAME `Q₁` (the NOT-(ii) pin).
§2 mass sign + the (i) collapse `_eq_deltaJ_comp_of_coarse_field_zero`; the characterization
`_massTerm_eq_zero_iff` (mass `=0 ↔ Q₁(CB̃)=0`); `_le_deltaJ_comp` (`a≥0 ⇒ form ≤ deltaJ∘C`);
vanishing on the gauge kernel `_eq_zero_of_mem_V`.
§3 genuine `U`-dependence of the composition (`a=0, C=id` transfer from `deltaKSuTwoForm`'s witness).
§4 the leading-term BRIDGE `cStarDeltaKC_coercivity_iff_leading` (reuse of
`deltaKSuTwoCoercivity_iff_shifted` at `A0 = C B̃`): the `C*Δ_kC ≥ γ₀` inequality is EXACTLY the
leading `deltaJ ≥ (γ₀+a)` inequality — the reduction to the leading term.
§5 the concrete-`C` coercivity TARGET (`def : Prop`, NOT proved), its NON-VACUITY guard
(`cStarDeltaKC_concrete_C_ne_zero`, reusing `reparamCSuTwo_ne_zero`: the pinned `C ≠ 0`, so it is not
the S91-vacuous free-`C=0`), and the concrete unconditional single-bond constraint on witness.

## Honesty / scope

* **ISLAND.** Nothing here is wired to `coerc_u_main` or any consumed spine declaration. NO coercivity
  is proved; the `C*Δ_kC ≥ γ₀` target is a bare `def : Prop`.
* **SINGLE-constraint `C`, PARTIAL.** The concrete `C` drops ONE bond of ONE coarse bond; the full
  (3.157) `C` drops one per coarse bond plus the axial bonds. Assembling the full `C` (hence the clean
  (i) collapse `C*Δ_kC = deltaJ∘C`) additionally needs almost-locality/decoupling and per-`c`
  invertibility ~~(NAMED in `ReparamCSuTwo`, not built)~~.
  **UPDATED (2026-07-26; retained struck):**
  at the CORRECTED dropped bond, decoupling IS built and general in `L`
  (`ReparamCDisjoint.droppedBondLast_not_reads`, `constraint_indep_of_other_droppedBond`); at the
  WRONG bond this module currently pins, decoupling is provably FALSE
  (`ReparamCDisjoint.droppedBond_not_decoupled`) and the joint system is singular for every `U`
  (`ReparamCJoint.witnessMain_joint_kernel_nonzero`) — so the full `C` is unreachable from
  `concreteWitnessC` as currently defined, and the retarget above is a PREREQUISITE, not an
  optimisation. For the single-constraint object here the mass is RETAINED.
* **`deltaJ = Δ_k` at `U=1` (NOT the leading term).** Per the grade-2 correction (SOL_VERDICT.md),
  `deltaJ` is the MINIMIZED curl `min_{QA=B}[curl]`, which equals `Δ_k` at `U=1` (the mass has
  cancelled); the pre-cancellation leading term `⟨B,(QG₁Q*)⁻¹B⟩` is `deltaJ + a‖B‖²`. So the faithful
  `⟨B̃,C*Δ_kC B̃⟩` at `U=1` is `deltaJ∘C = cStarDeltaKCForm 0`. The source term `−2⟨H₁D̃⁽²⁾(B),J⟩` is
  `0` at `J=0` (§3 residual of `DeltaKSuTwoAssembly`).
* **`covCoarseBondInner` faithfulness.** Equals `‖B‖²` only on COMPATIBLE full blocks; the ONE
  faithfulness-load-bearing statement (the coercivity target §5, `CStarDeltaKCConcreteCoercivity
  Target`) carries its own explicit `CompatibleExtent witnessL witnessEll →` hypothesis (mirroring the
  guard in `DeltaKSuTwoCoercivityTarget`); the algebraic bricks (§1–§4) hold for ALL `ell`.
-/

namespace AdalyFormal.Balaban.CStarDeltaKCCompose

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.Q1Real
  AdalyFormal.Balaban.CovariantHjFaithful
  AdalyFormal.Balaban.DeltaKSuTwoAssembly
  AdalyFormal.Balaban.ReparamCSuTwo
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (targetCoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the (3.157) `C*Δ_kC` sandwich on `B̃`, over a generic real-linear `C` -/

/-- **`⟨B̃, C*Δ_kC B̃⟩` (CMP99b (3.157)), su(2) carrier, at zero source.** The substitution `B = C B̃`
into the (3.156) `Δ_k` quadratic form: `cStarDeltaKCForm a … C B̃ = deltaKSuTwoForm a … (C B̃)`,
i.e. `⟨CB̃, Δ_k(CB̃)⟩`. Over a GENERIC real-linear reparametrization `C`; the concrete (3.157) `C` is
`ReparamCSuTwo.reparamCSuTwo` (instantiated in §5). The adjoint law `⟨B̃, C*MC B̃⟩ = ⟨CB̃, M(CB̃)⟩` is
automatic at the form level (no separate `C*` operator needed). -/
noncomputable def cStarDeltaKCForm (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo) : ℝ :=
  deltaKSuTwoForm a ell levels U (C Btil)

/-- **The composition, unfolded — the NOT-(ii) pin.** `cStarDeltaKCForm` is
`deltaJ∘C − a·⟨Q₁(CB̃), Q₁(CB̃)⟩` with `Q₁ = lineCoarseRestrictCovLM U ell` — the SAME `Q₁` whose
single-bond value `reparamCSuTwo`'s constraint zeros. No second coarse-graining map is involved. -/
theorem cStarDeltaKCForm_eq (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo) :
    cStarDeltaKCForm a ell levels U C Btil =
      deltaJQuadFormCovFaithful ell levels U (C Btil)
        - a * covCoarseBondInner (lineCoarseRestrictCovLM U ell (C Btil))
            (lineCoarseRestrictCovLM U ell (C Btil)) := by
  simp only [cStarDeltaKCForm, deltaKSuTwoForm]

#print axioms cStarDeltaKCForm_eq

/-! ## §2 — mass sign, the (i) collapse, the characterization, `≤ deltaJ∘C`, vanishing on `V` -/

/-- `covCoarseBondInner 0 0 = 0`. -/
theorem covCoarseBondInner_zero {ell : ℕ} :
    covCoarseBondInner (0 : CoarseBond L ell → SuTwo) 0 = 0 := by
  unfold covCoarseBondInner
  have hz : ∀ c : CoarseBond L ell,
      hsInner ((0 : CoarseBond L ell → SuTwo) c) ((0 : CoarseBond L ell → SuTwo) c) = 0 := by
    intro c
    rw [Pi.zero_apply, ← hsInnerLeftLM_apply]
    exact map_zero _
  rw [Finset.sum_congr rfl (fun c _ => hz c), Finset.sum_const_zero]

/-- **The mass term is `≥ 0`** (`covCoarseBondInner`-self-nonneg). -/
theorem cStarDeltaKCForm_massTerm_nonneg (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo) :
    0 ≤ covCoarseBondInner (lineCoarseRestrictCovLM U ell (C Btil))
          (lineCoarseRestrictCovLM U ell (C Btil)) :=
  covCoarseBondInner_self_nonneg _

/-- **THE (i) COLLAPSE, PROVED.** If the FULL covariant coarse field `Q₁(C B̃) = 0` (all coarse
bonds), the mass term vanishes and `cStarDeltaKCForm = deltaJ∘C`. This is the mechanism of Balaban's
FULL (3.157) `C`, which lands in `ker Q₁` (parametrizes `{B : …, Q₁B=0}`); there `C*Δ_kC = deltaJ∘C`.
The concrete single-constraint `C` built here does NOT satisfy this hypothesis (it kills only one
coarse-bond summand), so its mass is retained. -/
theorem cStarDeltaKCForm_eq_deltaJ_comp_of_coarse_field_zero (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo)
    (hzero : lineCoarseRestrictCovLM U ell (C Btil) = 0) :
    cStarDeltaKCForm a ell levels U C Btil = deltaJQuadFormCovFaithful ell levels U (C Btil) := by
  rw [cStarDeltaKCForm_eq, hzero, covCoarseBondInner_zero]
  ring

/-- **THE MASS-SURVIVAL CHARACTERIZATION.** The mass term vanishes IFF the FULL coarse field
`Q₁(C B̃) = 0` — `covCoarseBondInner` is positive-DEFINITE (`covCoarseBondInner_pos_of_ne`), not
merely PSD. Hence for the single-constraint concrete `C` (which forces only
`(Q₁(C B̃))(c₀)=0`, one of the 24 coarse bonds), the mass does NOT vanish in general: the collapse
(i) requires the full `C`. -/
theorem cStarDeltaKCForm_massTerm_eq_zero_iff (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo) :
    covCoarseBondInner (lineCoarseRestrictCovLM U ell (C Btil))
        (lineCoarseRestrictCovLM U ell (C Btil)) = 0
      ↔ lineCoarseRestrictCovLM U ell (C Btil) = 0 := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (covCoarseBondInner_pos_of_ne hne))
  · intro h
    rw [h, covCoarseBondInner_zero]

/-- **`a ≥ 0 ⇒ cStarDeltaKCForm ≤ deltaJ∘C`** — the mass subtraction can only lower the form. -/
theorem cStarDeltaKCForm_le_deltaJ_comp (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo) (ha : 0 ≤ a) :
    cStarDeltaKCForm a ell levels U C Btil ≤ deltaJQuadFormCovFaithful ell levels U (C Btil) := by
  rw [cStarDeltaKCForm_eq]
  have hmass := cStarDeltaKCForm_massTerm_nonneg ell U C Btil
  have : 0 ≤ a * covCoarseBondInner (lineCoarseRestrictCovLM U ell (C Btil))
      (lineCoarseRestrictCovLM U ell (C Btil)) := mul_nonneg ha hmass
  linarith

/-- **Vanishing when `C B̃` lands in the gauge kernel `V`.** Then BOTH the leading term and the coarse
field vanish (`deltaKSuTwoForm_eq_zero_of_mem_V`), so the sandwich is `0` for every `a`. -/
theorem cStarDeltaKCForm_eq_zero_of_mem_V (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo)
    (hV : C Btil ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    cStarDeltaKCForm a ell levels U C Btil = 0 :=
  deltaKSuTwoForm_eq_zero_of_mem_V a ell levels U (C Btil) hV

#print axioms cStarDeltaKCForm_eq_deltaJ_comp_of_coarse_field_zero
#print axioms cStarDeltaKCForm_massTerm_eq_zero_iff
#print axioms cStarDeltaKCForm_le_deltaJ_comp
#print axioms cStarDeltaKCForm_eq_zero_of_mem_V

/-! ## §3 — genuine `U`-dependence of the composition (scalar-carrier root-defect cure) -/

/-- **`U`-DEPENDENCE THROUGH THE (3.157) SANDWICH.** At `a=0, C=id, (ell,levels)=(1,[])` the two
backgrounds `myTrivialU ≠ witnessU` (same underlying `myWitnessConfig`) give DIFFERENT
`cStarDeltaKCForm` values, transferred through the composition from
`deltaKSuTwoForm_zero_mass_genuinely_U_dependent`. The su(2) carrier `Bond → SuTwo` HOSTS the
`U`-dependence that the convicted scalar `FaithfulCoercivity.lean` carrier could not, and it survives
the (3.157) sandwich. (The concrete (3.157) `C`-map is itself `U`-dependent — upstream
`ReparamCSuTwo.reparamCSuTwo_genuinely_U_dependent`.) -/
theorem cStarDeltaKCForm_genuinely_U_dependent :
    cStarDeltaKCForm 0 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        myTrivialU LinearMap.id myWitnessConfig ≠
      cStarDeltaKCForm 0 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        witnessU LinearMap.id myWitnessConfig := by
  show deltaKSuTwoForm 0 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        myTrivialU (LinearMap.id myWitnessConfig) ≠
      deltaKSuTwoForm 0 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        witnessU (LinearMap.id myWitnessConfig)
  rw [LinearMap.id_apply]
  exact deltaKSuTwoForm_zero_mass_genuinely_U_dependent

#print axioms cStarDeltaKCForm_genuinely_U_dependent

/-! ## §4 — the leading-term BRIDGE: `C*Δ_kC ≥ γ₀` is EXACTLY `deltaJ∘C ≥ (γ₀+a)` -/

/-- **THE REDUCTION TO THE LEADING TERM.** For any `γ₀`, the `C*Δ_kC` coercivity inequality
`γ₀·‖Q₁(CB̃)‖² ≤ cStarDeltaKCForm` is EQUIVALENT to the leading-term inequality
`(γ₀+a)·‖Q₁(CB̃)‖² ≤ deltaJ(C B̃)` — the mass subtraction is a constant shift of the required
coercivity constant. Reuse of `DeltaKSuTwoAssembly.deltaKSuTwoCoercivity_iff_shifted` at `A0 = C B̃`
(LAW-19). This is the promised "coercivity reduces to the leading-term `deltaJ ≥ γ'‖·‖²`". -/
theorem cStarDeltaKC_coercivity_iff_leading (a γ₀ : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)) (Btil : Bond L → SuTwo) :
    γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell (C Btil))
          (lineCoarseRestrictCovLM U ell (C Btil))
        ≤ cStarDeltaKCForm a ell levels U C Btil
      ↔ (γ₀ + a) * covCoarseBondInner (lineCoarseRestrictCovLM U ell (C Btil))
            (lineCoarseRestrictCovLM U ell (C Btil))
        ≤ deltaJQuadFormCovFaithful ell levels U (C Btil) := by
  rw [cStarDeltaKCForm]
  exact deltaKSuTwoCoercivity_iff_shifted a γ₀ ell levels U (C Btil)

#print axioms cStarDeltaKC_coercivity_iff_leading

/-! ## §5 — the CONCRETE (3.157) `C`: instantiation, unconditional single-bond constraint, the OPEN
coercivity TARGET, and its NON-VACUITY guard -/

/-- **⚠ PINNED TO THE WRONG DROPPED BOND (2026-07-26) — the one affected declaration in this
module.** ~~The concrete (3.157) `C` on the witness lattice.~~ (unconditional: `Dc_inv = ell⁴·id`,
its `hinv` discharged in `ReparamCSuTwo.coeffDc_witness_hinv`). This is the `C` the coercivity
target
is pinned to.

**What is still TRUE:** this IS a well-defined `LinearMap`, it IS unconditional (no assumed
inverse),
and every theorem below about it holds. **What is NOT true:** that it is CMP99b (3.157)'s `C`. It
drops `ReparamCSuTwo.droppedBond witnessEll targetCoarseBond = (witnessY, 0)`, the fine bond at
`μ`-offset `0`, whereas p.428's `b₀` is at offset `ell − 1` — at `witnessEll = 2` a DIFFERENT bond
(`ReparamCSuTwo.droppedBond_ne_lastOffset_witness`). Worse, the offset-`0` bond is itself the whole
of `staircasePath witnessY (witnessY + e₀)`, hence pinned to `0` by the axial gauge
(`ReparamCWiring.droppedBond_mem_staircase_witness`), so this `C` "solves" for a variable the gauge
already fixes. See the INHERITED CORRECTION at the top of this file for the corrected instantiation
and its `Dc_inv = (ell⁴/2) • RMap ((U_μ(y))⁻¹)`. NOT retargeted here (upstream write-scope). -/
noncomputable def concreteWitnessC :
    (Bond witnessL → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo) :=
  reparamCSuTwo witnessU witnessEll targetCoarseBond
    (droppedBond witnessEll targetCoarseBond) ((witnessEll : ℝ) ^ 4 • LinearMap.id)

/-- **The concrete `C` satisfies the single-bond (3.157) constraint UNCONDITIONALLY on witness**:
`(Q₁(witnessU)(concreteWitnessC B̃))(targetCoarseBond) = 0` for every `B̃`
(`ReparamCSuTwo.reparamCSuTwo_witness_constraint`). This zeros the `c₀`-summand of the mass term ONLY;
the other 23 coarse-bond summands are not constrained, so the mass is retained (see
`cStarDeltaKCForm_massTerm_eq_zero_iff`).
**SCOPE (2026-07-26):** a true theorem, but about the wrong-bond `C` (see `concreteWitnessC`). The
constraint `(Q₁(C B̃))(c₀)=0` is genuinely enforced; what it is not is (3.157)'s constraint at
(3.157)'s free variable. -/
theorem concreteWitnessC_constraint (Btil : Bond witnessL → SuTwo) :
    lineCoarseRestrictCov witnessU witnessEll (concreteWitnessC Btil) targetCoarseBond = 0 :=
  reparamCSuTwo_witness_constraint Btil

/-- **NON-VACUITY GUARD — the concrete `C ≠ 0`.** `CStarDeltaKCSuTwo.free_C_coercivity_target
_vacuous_at_zero_C` showed the degenerate `C=0` makes a free-`C` coercivity target vacuous (S91 /
`s91-existential-over-free-data`). The concrete `C` is provably NOT that map
(`ReparamCSuTwo.reparamCSuTwo_ne_zero`): it is the identity on every free bond. So the coercivity
target below, pinned to this `C`, is NOT S91-vacuous.
**SCOPE (2026-07-26):** unaffected in substance — `reparamCSuTwo_ne_zero` holds for ANY `Dc_inv` and
only uses `(site1,0) ≠ b₀`, so the same non-vacuity argument runs at the corrected bond; only the
particular `b₀` in the statement changes. -/
theorem cStarDeltaKC_concrete_C_ne_zero : concreteWitnessC ≠ 0 :=
  reparamCSuTwo_ne_zero _

/-- **THE `C*Δ_kC ≥ γ₀` COERCIVITY TARGET, pinned to the CONCRETE (3.157) `C` — REFUTED as written
(unrestricted `∀ B̃`).** Bounds `cStarDeltaKCForm a` below by `γ₀‖Q₁(concreteWitnessC B̃)‖²` over ALL
`B̃`. By `cStarDeltaKC_coercivity_iff_leading` it is EXACTLY the leading `deltaJ(C B̃) ≥ (γ₀+a)‖·‖²`
over all `B̃` — the same unrestricted `∀`-shape refuted for the leading target
(`U1LeadingCoercivity.faithfulCovCoercivityTarget_trivialU_witness_false`). It is pinned to
`witnessU` (not `trivialU`), so an in-file refutation needs a curl-free, nonzero-coarse-average `B̃`
under `witnessU`/`concreteWitnessC` — a NAMED sub-check, not built here. Regardless, this is NOT the
faithful `⟨B̃,C*Δ_kC B̃⟩` (that is `a=0`, `deltaJ∘C`), and the correct object is the domain-restricted
target in `CoercivityTargetsCorrected.lean`. `def : Prop` only — NOT asserted, NO proof, NOT wired.
**SCOPE (2026-07-26):** a THIRD reason not to pursue this target as written — it is pinned to
`concreteWitnessC`, which drops the wrong bond (see above). Any future version must be re-pinned to
the corrected `C` before its content is meaningful. -/
def CStarDeltaKCConcreteCoercivityTarget (a : ℝ) : Prop :=
  CompatibleExtent witnessL witnessEll →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ Btil : Bond witnessL → SuTwo,
      γ₀ * covCoarseBondInner
          (lineCoarseRestrictCovLM witnessU witnessEll (concreteWitnessC Btil))
          (lineCoarseRestrictCovLM witnessU witnessEll (concreteWitnessC Btil))
        ≤ cStarDeltaKCForm a witnessEll
            ([] : List (KernelSubspace.Level witnessL)) witnessU concreteWitnessC Btil

/-- **THE CONCRETE TARGET REDUCES, PER INPUT, TO THE LEADING TERM.** For each `B̃`, the concrete
`C*Δ_kC` coercivity inequality at constant `γ₀` is EXACTLY the leading `deltaJ` inequality at
`γ₀+a` — instantiation of the §4 bridge at `concreteWitnessC`. Confirms the target's genuine content
sits in the (open) leading-term coercivity, with the mass a constant shift. -/
theorem cStarDeltaKC_concrete_coercivity_iff_leading (a γ₀ : ℝ) (Btil : Bond witnessL → SuTwo) :
    γ₀ * covCoarseBondInner
          (lineCoarseRestrictCovLM witnessU witnessEll (concreteWitnessC Btil))
          (lineCoarseRestrictCovLM witnessU witnessEll (concreteWitnessC Btil))
        ≤ cStarDeltaKCForm a witnessEll ([] : List (KernelSubspace.Level witnessL))
            witnessU concreteWitnessC Btil
      ↔ (γ₀ + a) * covCoarseBondInner
            (lineCoarseRestrictCovLM witnessU witnessEll (concreteWitnessC Btil))
            (lineCoarseRestrictCovLM witnessU witnessEll (concreteWitnessC Btil))
        ≤ deltaJQuadFormCovFaithful witnessEll ([] : List (KernelSubspace.Level witnessL))
            witnessU (concreteWitnessC Btil) :=
  cStarDeltaKC_coercivity_iff_leading a γ₀ witnessEll ([] : List (KernelSubspace.Level witnessL))
    witnessU concreteWitnessC Btil

#print axioms concreteWitnessC_constraint
#print axioms cStarDeltaKC_concrete_C_ne_zero
#print axioms cStarDeltaKC_concrete_coercivity_iff_leading

end AdalyFormal.Balaban.CStarDeltaKCCompose
