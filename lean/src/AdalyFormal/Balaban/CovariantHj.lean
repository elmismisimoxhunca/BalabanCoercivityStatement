/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.SuTwoInner

set_option autoImplicit false

/-!
# The `D*D` term of `Δ_k(U)` on the COVARIANT `𝔰𝔲(2)`-valued carrier — CMP99b p.391-392, eq. (3.10)

**Task** (dispatch mandate): build `H_j`/`Δ_j` on the covariant carrier, against the covariant
curvature obstruction `Δ'` (CMP99b eq. 3.10), replacing `formal/AdalyFormal/DELTA_J_PINNING.md`'s
refuted flat pin. `Δ_j`'s real construction lives one stage EARLIER than `H_j`'s harmonic-extension
machinery: CMP99b (3.10) first builds `Δ^η(U)` (`⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ'A⟩`) as a quadratic form
on RAW bond configurations `A`, and `H_j`'s job (CMP95 p.29, `HjMinimizer.lean`'s existing flat
pattern) is to Schur-complement THIS operator against a constraint subspace. This module builds the
FIRST term, `⟨A,D*DA⟩`, faithfully on the covariant carrier and proves it is genuinely `U`-dependent
(the exact property `formal/AdalyFormal/DELTA_J_PINNING.md` proved the flat object structurally
lacks). `Δ'` (the second term) and the `H_j` extension/projection machinery are NAMED, NOT built —
see the two "Named residual" sections at the end.

## Source, read directly from a 300dpi render (LAW-11), not the `conf=0.44` mathpix machine-draft

Rendered `balaban_CMP99_1985_propagators_backgroundfield.pdf` pdf pages 3-4 = printed pp.391-392
myself (sha256 `39f8033b35838c7bdd14f97c7fb1edb0b35d4190b8b88f31d19d12a72d542861`, matching the hash
already pinned in `SuTwoInner.lean`'s own docstring — same source file, independently re-rendered).
VERBATIM, p.392, eq. (3.10):

> "The quadratic terms in the expansion (3.7) define the basic operator generalizing the operator
> `∂*∂` in the Abelian case. We denote it by `Δ^η(U)`, or simply by `Δ`. For `U` with values in the
> unitary group `U(N)` it is a hermitian operator given by the quadratic form
> `⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ'A⟩`,
> `⟨A,Δ'A⟩ = Σ_{p⊂T_η} η^d tr((D_U^1 A)(p))² η^{-2}(Re U(∂p) - 1)`
> `  + tr Σ_{b1,b2⊂∂(p)_z, b1≺b2} i[A'(b1),A'(b2)] η^{-2} Im U(∂p).`  (3.10)
> We have written it this way because with our assumptions on the configuration `U` the operator
> `Δ'` will be a bounded, small operator, which will be treated as a small perturbation of `D*D`."

Surrounding page (p.391, VERBATIM, last three lines, already quoted by `SuTwoInner.lean`): "In the
sequel we will frequently use adjoint operators to derivatives `D`. The adjoints are taken with
respect to natural `L²` scalar products for functions with values in `N×N` hermitian matrices." — so
`D` in `D*D` is exactly `CovariantOperators.curlValueCovariant` (eq. 3.4, already built there) and
`⟨A,D*DA⟩` is `‖DA‖²_{L²}`, the standard Gram identity — the route this module takes, matching
`HjMinimizer.lean`'s own `deltaJQuadForm := ‖curlCLM(...)‖²` pattern (CMP95 eq. 1.65), so no adjoint
OPERATOR needs to be constructed to state this term, only the `L²` norm-squared of the covariant
curl.

`AdalyFormal.Target.ClayStatement.periodicPlaquetteHolonomy` (`ClayStatement.lean:1286-1292`)
ALREADY builds `U(∂p) = U(x,μ)·U(shift_μ x,ν)·U(shift_ν x,μ)⁻¹·U(x,ν)⁻¹` for any `Group G` — exactly
CMP99b's `U(∂p)`, reused (LAW-19) in the `Δ'` residual note below, not rebuilt.

## Instance hazard — why NO `PiLp`/`InnerProductSpace` typeclass instance is registered here

`CovariantOperators.lean` §6/§7 already installs GLOBAL (non-scoped) `NormedAddCommGroup`/
`NormedSpace` instances on `Bond L → SuTwo` (sup norm) and on `PiLp 2 (fun _ : Bond L => SuTwo)`
(its own `BondFnL2`), both built from the SCOPED `Matrix.Norms.L2Operator` norm on the ambient
matrix type. `SuTwoInner.lean` installs a SEPARATE, independently-built `NormedAddCommGroup SuTwo`
(`hsInner`'s induced norm) and its own docstring states the two are "equal as functions... but not
definitionally so; the Lean proof of that agreement is named as a residual and NOT claimed." This
module imports BOTH files (`curlValueCovariant`/`RMap` from the first, `hsInner` and its positivity
from the second). Invoking Mathlib's generic `PiLp.innerProductSpace` on `BondFnL2 L` here would
silently produce a SECOND, different `NormedAddCommGroup (BondFnL2 L)` — an actual instance diamond
of exactly the kind `CovariantOperators.lean` §7 inspected and declined to create for `SuTwo` itself.
Neither existing lane resolved the underlying norm-agreement residual, so this module does not
attempt to either: it works with bare `Finset.sum`-of-`hsInner` FUNCTIONALS (`def`s, not typeclass
instances), which need no `NormedAddCommGroup`/`InnerProductSpace` registration. Consequence,
disclosed as `TIER E` below: `dstarDQuadForm` is a well-typed `ℝ`-valued quadratic form, faithfully
sourced, genuinely `U`-dependent (the deliverable) — but NOT (yet) promoted to the `H →L[ℝ] H`
`ContinuousLinearMap` shape `CoercivityHypothesis.Δ` ultimately needs; that promotion is named, not
attempted, and needs the SAME norm-diamond resolved first.

## What this module builds (TIER A/B, positive results)

1. **`covBondInner`/`covPlaqInner`** (§1) — the `L²` bilinear form on `Bond L → SuTwo` /
   `PeriodicLatticePlaquette L → SuTwo`, as a bare `Finset.sum` of `hsInner` (CMP99b p.391's "natural
   `L²` scalar products", the summation-over-the-lattice reading, not a typeclass instance).
2. **`dstarDQuadForm`** (§2) — CMP99b (3.10)'s `⟨A,D*DA⟩` term, `:= covPlaqInner (curl U A) (curl
   U A)`, together with `dstarDQuadForm_nonneg`.
3. **`curlValueCovariant_congr_of_ne`** (§3) — a GENERAL lemma (not specific to any witness): two
   link configurations agreeing outside `(x,0)` for a fixed base site `x` induce the SAME covariant
   curl at every plaquette NOT based at `x` in direction `0` — the mechanical fact that makes a
   single-link perturbation's effect on the FULL lattice sum tractable (at most 2 plaquettes, since
   `p.2.1.2 ≠ 0` always by the ordering `p.2.1.1 < p.2.1.2` on `Fin 3`).
4. **`dstarDQuadForm_genuinely_U_dependent`** (§4) — **THE HEADLINE RESULT**: a concrete two-bond
   witness configuration `A` on `AdmissibleSubspace.witnessL` with `dstarDQuadForm trivialU A ≠
   dstarDQuadForm witnessU A` — kernel-checked, `Δ_nonconstant`-shaped genuine `U`-dependence for a
   quadratic form sourced DIRECTLY from CMP99b (3.10)'s first term. This is the exact property
   `DELTA_J_PINNING.md` proved the flat `deltaJOp` structurally CANNOT have.

## Named residuals — NOT built (TIER C/D/E), stated precisely per BUILD DISCIPLINE #7 / OPS-1

* **TIER C — `Δ'` itself** (eq. 3.10's second line): needs (a) the "hermitian presentation" `A'` of a
  bond field `A` (CMP99b's `A' = iA`-type transform between the anti-hermitian `𝔰𝔲(2)` carrier this
  tree uses and the hermitian carrier `Δ'`'s formula is written in — `SuTwoInner.lean`'s own docstring
  names exactly this transport, `φ : X ↦ iX`, but only for the INNER PRODUCT, not for `Δ'`'s
  commutator term); (b) `Re U(∂p)`/`Im U(∂p)` as MATRIX-valued objects (buildable from
  `periodicPlaquetteHolonomy`, not attempted here); (c) the exact bilinear-pairing structure of
  `tr((D_U^1A)(p))²·(Re U(∂p)-1)` — a NONABELIAN matrix product whose precise associativity/ordering
  is genuinely ambiguous even after my own direct 300dpi image read (OCR confidence on this specific
  display is `0.44`, the lowest on either page, and cross-referencing Bałaban's `A'` convention
  against his `tr`/hermitian-presentation choice elsewhere in the paper was not completed within this
  dispatch's time budget). Attempting a guess here risks the exact silent-wrong-encoding failure mode
  (§LEAN-D) this project's own build discipline warns against hardest — named and stopped, not
  guessed.
* **TIER D — `H_j` on the covariant carrier**: `HjMinimizer.lean`'s flat construction needs a
  constraint subspace `V := ker(Q_j) ⊓ ker(R∘∂*)` and its image `W := ∂₁(V)`, built from the FLAT,
  `U`-INDEPENDENT `coarseRestrictCLM`/`RProj`/`gradCLM` (`KernelSubspace.lean`/`AdmissibleSubspace.lean`
  /`LatticeOperators.lean`). On the covariant carrier, `Q_j`/`R` themselves would need `U`-dependent
  analogs (there is no "coarse-graining" or "gauge-fixing projection" construction anywhere in this
  tree for `𝔰𝔲(2)`-valued fields) — a genuinely new construction, not a port, exactly the gap
  `DELTA_J_PINNING.md`'s own "THE REAL BLOCKER" section named. NOT attempted here.
* **TIER E — operator promotion**: `dstarDQuadForm` is a quadratic FORM (`(Bond L → SuTwo) → ℝ`), not
  an `H →L[ℝ] H` `ContinuousLinearMap` — see the instance-hazard note above for exactly why (the
  `SuTwo` `NormedAddCommGroup` diamond between `CovariantOperators.lean` and `SuTwoInner.lean`, itself
  a residual NEITHER prior lane resolved). Promoting it to `CoercivityHypothesis.Δ`'s exact type needs
  that diamond resolved first (build `InnerProductSpace ℝ (Bond L → SuTwo)` COMPATIBLE with
  `CovariantOperators.instNormedAddCommGroupBondFn`, not a fresh one) — not attempted here.
-/

namespace AdalyFormal.Balaban.CovariantHj

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the `L²` bilinear forms, as bare `Finset.sum`s of `hsInner` (see instance-hazard note
in the module docstring for why this is NOT a `PiLp`/typeclass instance). -/

/-- **CMP99b p.391's "natural `L²` scalar product"**, on `Bond L → 𝔰𝔲(2)`, as an explicit sum. -/
noncomputable def covBondInner (A B : Bond L → SuTwo) : ℝ :=
  ∑ b : Bond L, hsInner (A b) (B b)

/-- The same, on `PeriodicLatticePlaquette L → 𝔰𝔲(2)` (the codomain of the covariant curl). -/
noncomputable def covPlaqInner (A B : PeriodicLatticePlaquette L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, hsInner (A p) (B p)

theorem covBondInner_self_nonneg (A : Bond L → SuTwo) : 0 ≤ covBondInner A A := by
  unfold covBondInner
  exact Finset.sum_nonneg (fun b _ => hsInner_self_nonneg (A b))

theorem covPlaqInner_self_nonneg (A : PeriodicLatticePlaquette L → SuTwo) :
    0 ≤ covPlaqInner A A := by
  unfold covPlaqInner
  exact Finset.sum_nonneg (fun p _ => hsInner_self_nonneg (A p))

theorem covPlaqInner_symm (A B : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner A B = covPlaqInner B A := by
  unfold covPlaqInner
  exact Finset.sum_congr rfl (fun p _ => hsInner_symm (A p) (B p))

#print axioms covBondInner_self_nonneg
#print axioms covPlaqInner_self_nonneg
#print axioms covPlaqInner_symm

/-! ## §2 — the `D*D` term of CMP99b (3.10), `⟨A,D*DA⟩ = ‖DA‖²_{L²}` -/

/-- **CMP99b (3.10)'s FIRST term, `⟨A,D*DA⟩`**, built via the standard Gram identity
`⟨A,D*DA⟩ = ‖DA‖²` rather than constructing `D*` as an operator (matching `HjMinimizer.lean`'s own
`deltaJQuadForm := ‖curlCLM(...)‖²`, CMP95 eq. 1.65, the SAME move one level up the construction). -/
noncomputable def dstarDQuadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  covPlaqInner (curlValueCovariant U A) (curlValueCovariant U A)

theorem dstarDQuadForm_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : 0 ≤ dstarDQuadForm U A :=
  covPlaqInner_self_nonneg _

#print axioms dstarDQuadForm_nonneg

/-! ## §3 — a general lemma: a single-link perturbation at `(x,0)` changes the covariant curl at
NO plaquette `p` with `p.1 ≠ x ∨ p.2.1.1 ≠ 0` -/

/-- **`p.2.1.2 ≠ 0` always**, from the defining order `p.2.1.1 < p.2.1.2` on `Fin 3`. The fact that
makes a single-link change at direction `0` reachable by at most the `p.2.1.1 = 0` case, never the
`p.2.1.2` position. -/
theorem plaquette_snd_dir_ne_zero (p : PeriodicLatticePlaquette L) : p.2.1.2 ≠ (0 : Fin 3) := by
  intro h
  have hlt := p.2.2
  rw [h] at hlt
  exact absurd hlt (Fin.not_lt.mpr (Fin.zero_le _))

/-- **Two link configurations agreeing EVERYWHERE except possibly at the single bond `(x,0)`
induce the SAME covariant curl at every plaquette `p` with `p.1 ≠ x ∨ p.2.1.1 ≠ 0`.** The `D_U`
formula's only two `U`-dependent slots are `U(p.1,p.2.1.1)` (term 2) and `U(p.1,p.2.1.2)` (term 3);
term 3's slot can never equal `(x,0)` (§3's previous lemma, for ANY `x`), and term 2's slot equals
`(x,0)` only when `p.1 = x ∧ p.2.1.1 = 0`. -/
theorem curlValueCovariant_congr_of_agree_off_dir0
    (U1 U2 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L)
    (hagree : ∀ e : Bond L, e ≠ (x, (0 : Fin 3)) → U1 e = U2 e)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (hp : p.1 ≠ x ∨ p.2.1.1 ≠ 0) :
    curlValueCovariant U1 A p = curlValueCovariant U2 A p := by
  have h2 : U1 (p.1, p.2.1.2) = U2 (p.1, p.2.1.2) := by
    apply hagree
    intro hcontra
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcontra)
  have h1 : U1 (p.1, p.2.1.1) = U2 (p.1, p.2.1.1) := by
    apply hagree
    intro hcontra
    rcases hp with hp1 | hp1
    · exact hp1 (congrArg Prod.fst hcontra)
    · exact hp1 (congrArg Prod.snd hcontra)
  unfold curlValueCovariant
  rw [h1, h2]

#print axioms plaquette_snd_dir_ne_zero
#print axioms curlValueCovariant_congr_of_agree_off_dir0

/-! ## §4 — THE HEADLINE RESULT: a concrete witness proving `dstarDQuadForm` genuinely
`U`-dependent, on `AdmissibleSubspace.witnessL` (reusing `CovariantOperators.witnessU`/
`witnessMElem`/`witnessPlaquette`/`suTwoWitness`, LAW-19) -/

/-- The trivial (all-identity) link configuration, the natural comparison point for `witnessU`
(which already IS the trivial configuration everywhere except one link). -/
noncomputable def myTrivialU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  fun _ => 1

/-- The bond entering `curlValueCovariant`'s CONJUGATED "term 2" position at `witnessPlaquette`. -/
def myWitnessB0 : Bond AdmissibleSubspace.witnessL :=
  (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))

/-- The bond entering `curlValueCovariant`'s UNCONJUGATED "term 4" position at `witnessPlaquette`. -/
def myWitnessB1 : Bond AdmissibleSubspace.witnessL := (AdmissibleSubspace.witnessY, (1 : Fin 3))

/-- **The two-bond test configuration**: `suTwoWitness` on both `myWitnessB0`/`myWitnessB1`, zero
elsewhere. Chosen so the CONJUGATED and UNCONJUGATED contributions at `witnessPlaquette` cancel
under the trivial configuration (giving `0`) but ADD under `witnessU` (giving `-2•suTwoWitness`,
since `R(M)` sends `suTwoWitness ↦ -suTwoWitness`) — a genuine, non-vacuous quadratic-form gap, not
merely a sign flip on a single spike (which the squared norm would not detect, `R` being an
isometry). -/
noncomputable def myWitnessConfig : Bond AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = myWitnessB0 then suTwoWitness else if e = myWitnessB1 then suTwoWitness else 0

theorem myWitnessB0_ne_b1 : myWitnessB0 ≠ myWitnessB1 := by decide

theorem myWitnessConfig_at_b0 : myWitnessConfig myWitnessB0 = suTwoWitness := by
  simp [myWitnessConfig]

theorem myWitnessConfig_at_b1 : myWitnessConfig myWitnessB1 = suTwoWitness := by
  simp only [myWitnessConfig]
  rw [if_neg (Ne.symm myWitnessB0_ne_b1)]
  simp

theorem myWitnessConfig_at_x0 :
    myWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) = 0 := by
  simp only [myWitnessConfig]
  rw [if_neg (by decide), if_neg (by decide)]

theorem myWitnessConfig_at_x2 :
    myWitnessConfig (AdmissibleSubspace.witnessY, (2 : Fin 3)) = 0 := by
  simp only [myWitnessConfig]
  rw [if_neg (by decide), if_neg (by decide)]

theorem myWitnessConfig_at_shift1_0 :
    myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)) = 0 := by
  simp only [myWitnessConfig]
  rw [if_neg (by decide), if_neg (by decide)]

theorem myWitnessConfig_at_shift0_2 :
    myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3)) = 0 := by
  simp only [myWitnessConfig]
  rw [if_neg (by decide), if_neg (by decide)]

theorem myWitnessConfig_at_shift2_0 :
    myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3)) = 0 := by
  simp only [myWitnessConfig]
  rw [if_neg (by decide), if_neg (by decide)]

#print axioms myWitnessB0_ne_b1
#print axioms myWitnessConfig_at_b0
#print axioms myWitnessConfig_at_b1
#print axioms myWitnessConfig_at_x0
#print axioms myWitnessConfig_at_x2
#print axioms myWitnessConfig_at_shift1_0
#print axioms myWitnessConfig_at_shift0_2
#print axioms myWitnessConfig_at_shift2_0

/-- The SECOND plaquette based at `witnessY` in direction `0` (`ν=2` instead of `witnessPlaquette`'s
`ν=1`) — the only other plaquette `curlValueCovariant_congr_of_agree_off_dir0` cannot reach. -/
def myWitnessPlaquette2 : PeriodicLatticePlaquette AdmissibleSubspace.witnessL :=
  (AdmissibleSubspace.witnessY, ⟨(0, 2), by decide⟩)

/-- The covariant curl of the test config vanishes at `witnessPlaquette` under the TRIVIAL
configuration: the conjugated and unconjugated contributions cancel exactly. -/
theorem curl_triv_at_witnessPlaquette :
    curlValueCovariant myTrivialU myWitnessConfig witnessPlaquette = 0 := by
  show myWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (myTrivialU (AdmissibleSubspace.witnessY, (0 : Fin 3))) (myWitnessConfig myWitnessB0) -
      RMap (myTrivialU (AdmissibleSubspace.witnessY, (1 : Fin 3)))
        (myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))) -
      myWitnessConfig myWitnessB1 = 0
  rw [myWitnessConfig_at_x0, myWitnessConfig_at_b0, myWitnessConfig_at_shift1_0,
    myWitnessConfig_at_b1]
  simp only [myTrivialU, RMap_one, LinearMap.id_coe, id_eq, map_zero]
  abel

/-- The covariant curl of the SAME test config at `witnessPlaquette` under `witnessU`: the
conjugated term FLIPS SIGN (`R(M)suTwoWitness = -suTwoWitness`) while the unconjugated term does
not — the two contributions now ADD instead of cancelling. -/
theorem curl_witnessU_at_witnessPlaquette :
    curlValueCovariant witnessU myWitnessConfig witnessPlaquette =
      -suTwoWitness - suTwoWitness := by
  show myWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3))) (myWitnessConfig myWitnessB0) -
      RMap (witnessU (AdmissibleSubspace.witnessY, (1 : Fin 3)))
        (myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))) -
      myWitnessConfig myWitnessB1 = -suTwoWitness - suTwoWitness
  rw [myWitnessConfig_at_x0, myWitnessConfig_at_b0, myWitnessConfig_at_shift1_0,
    myWitnessConfig_at_b1, witnessU_at_x_mu, witnessU_at_x_nu, RMap_witnessMElem, RMap_one]
  simp only [LinearMap.id_coe, id_eq, map_zero]
  abel

/-- Both configurations agree (both give `0`) at `myWitnessPlaquette2` — the test config is not
supported on any bond that `myWitnessPlaquette2`'s formula reads. -/
theorem curl_triv_at_witnessPlaquette2 :
    curlValueCovariant myTrivialU myWitnessConfig myWitnessPlaquette2 = 0 := by
  show myWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (myTrivialU (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3))) -
      RMap (myTrivialU (AdmissibleSubspace.witnessY, (2 : Fin 3)))
        (myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3))) -
      myWitnessConfig (AdmissibleSubspace.witnessY, (2 : Fin 3)) = 0
  rw [myWitnessConfig_at_x0, myWitnessConfig_at_shift0_2, myWitnessConfig_at_shift2_0,
    myWitnessConfig_at_x2]
  simp

theorem curl_witnessU_at_witnessPlaquette2 :
    curlValueCovariant witnessU myWitnessConfig myWitnessPlaquette2 = 0 := by
  show myWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3))) -
      RMap (witnessU (AdmissibleSubspace.witnessY, (2 : Fin 3)))
        (myWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3))) -
      myWitnessConfig (AdmissibleSubspace.witnessY, (2 : Fin 3)) = 0
  rw [myWitnessConfig_at_x0, myWitnessConfig_at_shift0_2, myWitnessConfig_at_shift2_0,
    myWitnessConfig_at_x2, map_zero, map_zero]
  simp

#print axioms curl_triv_at_witnessPlaquette
#print axioms curl_witnessU_at_witnessPlaquette
#print axioms curl_triv_at_witnessPlaquette2
#print axioms curl_witnessU_at_witnessPlaquette2

/-- Bilinear expansion helper: `hsInner (r•X) (r•X) = r² * hsInner X X`, from `hsInner`'s already-
proved symmetry and left-linearity (§3/§4 of `SuTwoInner.lean`, LAW-19). -/
theorem hsInner_smul_smul (r : ℝ) (X : SuTwo) : hsInner (r • X) (r • X) = r ^ 2 * hsInner X X := by
  rw [hsInner_smul_left, hsInner_symm X (r • X), hsInner_smul_left]
  ring

theorem neg_sub_self_eq_smul (X : SuTwo) : -X - X = (-2 : ℝ) • X := by module

theorem hsInner_suTwoWitness_self : hsInner suTwoWitness suTwoWitness = 1 := hsInner_e3_e3

theorem hsInner_zero_zero : hsInner (0 : SuTwo) 0 = 0 := by
  have h := hsInner_smul_left (0 : SuTwo) (0 : SuTwo) (0 : ℝ)
  simpa using h

/-- `hsInner (-suTwoWitness - suTwoWitness) (-suTwoWitness - suTwoWitness) = 4`. -/
theorem hsInner_witnessU_plaquette_val :
    hsInner (-suTwoWitness - suTwoWitness : SuTwo) (-suTwoWitness - suTwoWitness) = 4 := by
  rw [neg_sub_self_eq_smul, hsInner_smul_smul, hsInner_suTwoWitness_self]
  norm_num

/-- **Uniqueness of the two exceptional plaquettes**: any `p` based at `witnessY` with
`p.2.1.1 = 0` is EITHER `witnessPlaquette` (`ν=1`) OR `myWitnessPlaquette2` (`ν=2`) — the only two
options once `p.2.1.1 < p.2.1.2` on `Fin 3` is combined with `p.2.1.1 = 0`. -/
theorem eq_witnessPlaquette_or_myWitnessPlaquette2
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (h1 : p.1 = AdmissibleSubspace.witnessY) (h2 : p.2.1.1 = (0 : Fin 3)) :
    p = witnessPlaquette ∨ p = myWitnessPlaquette2 := by
  have hlt := p.2.2
  rw [h2] at hlt
  have hval : p.2.1.2.val = 1 ∨ p.2.1.2.val = 2 := by
    have h3 : p.2.1.2.val < 3 := p.2.1.2.isLt
    have h4 : 0 < p.2.1.2.val := hlt
    omega
  rcases hval with hval | hval
  · left
    have h3 : p.2.1.2 = (1 : Fin 3) := Fin.ext hval
    have hpair : p.2.1 = ((0 : Fin 3), (1 : Fin 3)) := Prod.ext h2 h3
    have hsub : p.2 = witnessPlaquette.2 := Subtype.ext hpair
    exact Prod.ext h1 hsub
  · right
    have h3 : p.2.1.2 = (2 : Fin 3) := Fin.ext hval
    have hpair : p.2.1 = ((0 : Fin 3), (2 : Fin 3)) := Prod.ext h2 h3
    have hsub : p.2 = myWitnessPlaquette2.2 := Subtype.ext hpair
    exact Prod.ext h1 hsub

#print axioms eq_witnessPlaquette_or_myWitnessPlaquette2

/-- **Away from the two exceptional plaquettes, the covariant curl of the test config agrees
between `myTrivialU` and `witnessU`.** -/
theorem curl_agree_off_exceptional (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL)
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) :
    curlValueCovariant myTrivialU myWitnessConfig p =
      curlValueCovariant witnessU myWitnessConfig p := by
  refine curlValueCovariant_congr_of_agree_off_dir0 myTrivialU witnessU
    AdmissibleSubspace.witnessY ?_ myWitnessConfig p ?_
  · intro e he
    show (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = witnessU e
    unfold witnessU
    rw [if_neg he]
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 h1 h2 with h | h
    · exact hp1 h
    · exact hp2 h

#print axioms curl_agree_off_exceptional

/-- The per-plaquette summand of `hsInner (curl U A ·) (curl U A ·)` agrees pointwise between the
two configurations off the two-element exceptional set. -/
theorem hsInner_curl_agree_off_exceptional (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL)
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) :
    hsInner (curlValueCovariant myTrivialU myWitnessConfig p)
        (curlValueCovariant myTrivialU myWitnessConfig p) =
      hsInner (curlValueCovariant witnessU myWitnessConfig p)
        (curlValueCovariant witnessU myWitnessConfig p) := by
  rw [curl_agree_off_exceptional p hp1 hp2]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- **THE HEADLINE RESULT**: `dstarDQuadForm`, CMP99b (3.10)'s `⟨A,D*DA⟩` term built directly on
the covariant carrier, is GENUINELY `U`-dependent — the exact `Δ_nonconstant`-shaped property
`DELTA_J_PINNING.md` proved the flat `deltaJOp` structurally lacks (`deltaJOp_pin_unsatisfiable`).
The full lattice sum reduces to the two-element set `{witnessPlaquette, myWitnessPlaquette2}`
(`hsInner_curl_agree_off_exceptional` cancels every other plaquette in the difference), on which
`myWitnessPlaquette2` contributes `0` in both configurations and `witnessPlaquette` contributes `0`
under the trivial configuration and `4` under `witnessU`. -/
theorem dstarDQuadForm_genuinely_U_dependent :
    dstarDQuadForm myTrivialU myWitnessConfig ≠ dstarDQuadForm witnessU myWitnessConfig := by
  set S : Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL) :=
    {witnessPlaquette, myWitnessPlaquette2} with hS
  set fTriv : PeriodicLatticePlaquette AdmissibleSubspace.witnessL → ℝ :=
    fun p => hsInner (curlValueCovariant myTrivialU myWitnessConfig p)
      (curlValueCovariant myTrivialU myWitnessConfig p) with hfTriv
  set fWit : PeriodicLatticePlaquette AdmissibleSubspace.witnessL → ℝ :=
    fun p => hsInner (curlValueCovariant witnessU myWitnessConfig p)
      (curlValueCovariant witnessU myWitnessConfig p) with hfWit
  have hSsub : S ⊆ Finset.univ := Finset.subset_univ _
  have hsdiffEq : ∑ p ∈ Finset.univ \ S, fTriv p = ∑ p ∈ Finset.univ \ S, fWit p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_sdiff, hS, Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    exact hsInner_curl_agree_off_exceptional p hp.2.1 hp.2.2
  have htrivSplit := Finset.sum_sdiff (f := fTriv) hSsub
  have hwitSplit := Finset.sum_sdiff (f := fWit) hSsub
  have hStriv : ∑ p ∈ S, fTriv p = 0 := by
    rw [hS, Finset.sum_pair (by
      show witnessPlaquette ≠ myWitnessPlaquette2
      decide)]
    show hsInner (curlValueCovariant myTrivialU myWitnessConfig witnessPlaquette)
        (curlValueCovariant myTrivialU myWitnessConfig witnessPlaquette) +
      hsInner (curlValueCovariant myTrivialU myWitnessConfig myWitnessPlaquette2)
        (curlValueCovariant myTrivialU myWitnessConfig myWitnessPlaquette2) = 0
    rw [curl_triv_at_witnessPlaquette, curl_triv_at_witnessPlaquette2, hsInner_zero_zero]
    ring
  have hSwit : ∑ p ∈ S, fWit p = 4 := by
    rw [hS, Finset.sum_pair (by
      show witnessPlaquette ≠ myWitnessPlaquette2
      decide)]
    show hsInner (curlValueCovariant witnessU myWitnessConfig witnessPlaquette)
        (curlValueCovariant witnessU myWitnessConfig witnessPlaquette) +
      hsInner (curlValueCovariant witnessU myWitnessConfig myWitnessPlaquette2)
        (curlValueCovariant witnessU myWitnessConfig myWitnessPlaquette2) = 4
    rw [curl_witnessU_at_witnessPlaquette, curl_witnessU_at_witnessPlaquette2,
      hsInner_witnessU_plaquette_val, hsInner_zero_zero]
    ring
  intro heq
  unfold dstarDQuadForm covPlaqInner at heq
  have hfin : Finset.sum Finset.univ fTriv = Finset.sum Finset.univ fWit := heq
  rw [← htrivSplit, ← hwitSplit, hsdiffEq, hStriv, hSwit] at hfin
  norm_num at hfin

#print axioms dstarDQuadForm_genuinely_U_dependent

end AdalyFormal.Balaban.CovariantHj
