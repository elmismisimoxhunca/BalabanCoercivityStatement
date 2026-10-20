/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHj

set_option autoImplicit false

/-
================================================================================================
 CONVICTION BANNER — filed 2026-07-26, de-correlated Sol prosecution
 `compute/sol_deltaprime/SOL_PROSECUTION_DELTAPRIME.md`, Attack 1 A1.4 — verdict CONVICTED
================================================================================================
CMP99b printed p.392, on the SAME page as eq. (3.10) and under the SAME convention, states
verbatim: "Let us recall that the trace is normalized, i.e., `tr 1 = 1`."  For `N = 2` that means
source `tr = (1/2)·Tr`, while Mathlib's `Matrix.trace` is ordinary `Tr` with `Tr 1 = 2`.

Every `Δ′` term in THIS FILE — `deltaPrimeFirstTerm`, `deltaPrimeSecondTerm`, and their
`…Transported` variants, hence `deltaPrimeQuadForm` and `deltaPrimeQuadFormTransported` — uses RAW
`Matrix.trace` with no `1/2`.  They are therefore **twice** the source-normalized `Δ′`.  This is
NOT a harmless overall rescaling: `CovariantHj.dstarDQuadForm` is built entirely from
`SuTwoInner.hsInner = -(1/2)·Tr`, so the `D*D` half ALREADY carries the source normalization, and
the RELATIVE coefficient in `Δ_k = D*D + Δ′` is wrong by 2.

INTENDED REPAIR (this pass): the raw objects in this file are RETAINED unchanged (they are the
literal transcription of the printed expression against Mathlib's `Matrix.trace`, and several
downstream modules consume them by name).  The normalized objects already exist, kernel-checked and
general in `U`/`A`, in `Balaban/NormalizationAudit.lean` §1 —
`deltaPrimeQuadFormNormalizedTransported U A = (1/2) * deltaPrimeQuadFormTransported U A`
(`NormalizationAudit.lean:193-202`, predating this conviction).  Per LAW-19 that lemma is CONSUMED,
not re-derived.  The operator chain in `Balaban/DeltaPrimeOperator.lean` is re-routed through the
NORMALIZED form; see that file's own banner for the option taken and what changed meaning.

READ EVERY `deltaPrimeQuadForm*`/`deltaPrime*Term*` NAME IN THIS FILE AS RAW (= 2× source).  The
source-normalized objects are the `…Normalized…` ones in `NormalizationAudit.lean` and the
`…Normalized…` operator layer in `DeltaPrimeOperator.lean` §N.
================================================================================================
-/

/-!
# `Δ′` — the second term of CMP99b eq. (3.10), and the full assembly `Δ = D*D + Δ′`

**Task**: build `Δ′` faithfully (per `compute/delta_prime_read/DELTA_PRIME.md`'s settled read of
CMP99b printed pp.390-392), and assemble `⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ′A⟩`. `⟨A,D*DA⟩`
(`dstarDQuadForm`) is REUSED unchanged from `CovariantHj.lean` (LAW-19).

See `formal/AdalyFormal/DELTA_PRIME_BUILD.md` for the full plaquette-convention correspondence,
read directly off printed p.390 (not re-derived from the telescoping proof, per BUILD DISCIPLINE
#1). Summary: base site `x = p.1`, `μ = p.2.1.1`, `ν = p.2.1.2`, `y = shift_μ(x)`, `w = shift_ν(x)`,
`z` = far corner. `A′`'s four defining bond-values (CMP99b eq. 3.2, `U₀` renamed `U` per p.391)
translate to this tree's four `curlValueCovariant` sub-terms:

* `A′(x,y) = A(x,y)` (direct read, `T1`)
* `A′(y,z) = R(U(x,y))·A(y,z)` (`T2`, conjugated)
* `A′(z,w) = R(U(x,w))·A(z,w) = -R(U(x,w))·(T3)` (antisymmetry flips the sign: the STORED bond is
  `(w,z)`, not `(z,w)`)
* `A′(w,x) = A(w,x) = -(T4)` (antisymmetry: STORED bond is `(x,w)`)

Summing these four reproduces `curlValueCovariant` EXACTLY (`sum_Aprime_eq_curl` below), confirming
`(D_U^1 A)(p) = curlValueCovariant U A p` — `D_U^1` is not a new operator (`DELTA_PRIME.md`'s
finding, independently re-derived here).

`≺`-order on `∂(p)_z`'s bonds (p.390 prose: "a natural ordering... of the oriented contour
`∂(p)_z = ⟨z,w⟩∪⟨w,x⟩∪⟨x,y⟩∪⟨y,z⟩`" — the listing order IS the order): `(z,w)≺(w,x)≺(x,y)≺(y,z)`,
i.e. `A′_1=A′(z,w), A′_2=A′(w,x), A′_3=A′(x,y), A′_4=A′(y,z)`, commutator sum over the 6 pairs
`i<j`.

`U(∂p)` (eq. 3.10's un-subscripted `∂p`, matching `D_U^1`'s OWN basepoint `x`, not the `z`-based
`∂(p)_z` used only for A′'s bond LABELS) is `ClayStatement.periodicPlaquetteHolonomy U p`
(LAW-19, already built for a general `Group G`).

## Convention inherited from `CovariantOperators.lean`/`CovariantHj.lean`, NOT re-litigated here

CMP99b's own `A` is Hermitian (`U′=exp(iηA)`, p.390); this tree's `SuTwo` carrier is
ANTI-Hermitian (`SuTwoInner.lean`'s own docstring). The two presentations are related by the
`ℝ`-linear iso `φ:X↦iX`. `curlValueCovariant`/`dstarDQuadForm` were ALREADY built (and banked) by
substituting `SuTwo` values DIRECTLY into Bałaban's formula shapes with NO `φ`-transport
correction (only `hsInner`, used for inner products, carries `φ`'s sign). `Δ′` below inherits the
SAME convention (LAW-19: match established precedent). **Named residual, flagged not hidden**: for
a quantity QUADRATIC in `A` (unlike the LINEAR `curlValueCovariant` itself), the `φ`-transport
would introduce a `φ(X)² = (iX)² = -X²` sign, so `Δ′` AS LITERALLY WRITTEN BY BAŁABAN (in terms of
his Hermitian `A`) equals the NEGATIVE of what this file computes by direct substitution of `SuTwo`
values. This file does NOT apply that correction, for consistency with the already-banked
`dstarDQuadForm` (which uses the same "no transport" convention throughout `curlValueCovariant`).
Whether the untransported or transported sign is the one that makes `Δ = D*D + Δ′` an honestly
POSITIVE (Bałaban states `Δ` is a hermitian operator, and `Δ′` is meant to be "small" relative to
`D*D`, not sign-flipping it) is EXPLICITLY NOT decided here — see the final report's "Named
residuals" section.
-/

namespace AdalyFormal.Balaban.DeltaPrime

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `Re U(∂p)`, `Im U(∂p)` as matrix-valued objects (CMP99b eq. 3.7's own displayed
definitions, image-confirmed by `DELTA_PRIME.md`), built from `periodicPlaquetteHolonomy` (LAW-19,
reused from `ClayStatement.lean`, not rebuilt). -/

/-- `U(∂p)` as an explicitly-typed `SU(2)` element — a named intermediate so `reHolonomy`/
`imHolonomy` can be rewritten directly by a holonomy-value theorem, without fighting a `let`. -/
noncomputable def holonomyElem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  periodicPlaquetteHolonomy U p

/-- `U(∂p)⁻¹`, the GROUP inverse (`Matrix.specialUnitaryGroup`'s own `Inv`, i.e. `star`), taken
BEFORE any coercion to `Matrix`. **Named separately and deliberately** — `Matrix (Fin 2) (Fin 2) ℂ`
carries its OWN (nonsingular/adjugate) `Inv` instance, and writing `((holonomyElem U p)⁻¹ :
Matrix ...)` invites the elaborator to coerce `holonomyElem U p` to `Matrix` FIRST (to match the
type ascription) and apply the MATRIX ring inverse instead of the group one — a real elaboration
hazard hit and fixed in this file (they coincide only at the identity, which is why the
`trivialU`-background proofs in §5 did not expose it). This `def` forces group-level inversion by
construction: its RESULT type is `Matrix.specialUnitaryGroup`, not `Matrix`. -/
noncomputable def holonomyElemInv
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  (holonomyElem U p)⁻¹

/-- **`Re U(∂p) := ½(U(∂p) + U(∂p)⁻¹)`**, as a `2×2` complex matrix. -/
noncomputable def reHolonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) •
    ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) +
      (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ))

/-- **`Im U(∂p) := (1/2i)(U(∂p) - U(∂p)⁻¹)`**, as a `2×2` complex matrix. -/
noncomputable def imHolonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (2 * Complex.I) : ℂ) •
    ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) -
      (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ))

/-! ## §2 — `A′`'s four bond-values, directly against `curlValueCovariant`'s own four sub-terms -/

/-- `A′(x,y) = A(x,y)` — the direct read, no conjugation. -/
noncomputable def AprimeXY (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : SuTwo :=
  A (p.1, p.2.1.1)

/-- `A′(y,z) = R(U(x,y))·A(y,z)`. -/
noncomputable def AprimeYZ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : SuTwo :=
  RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))

/-- `A′(z,w) = R(U(x,w))·A(z,w) = -R(U(x,w))·A(w,z)` (antisymmetry `A(z,w)=-A(w,z)`; the STORED
bond is `(w,z)`, read as `A(shift_ν p.1, p.2.1.1)`). -/
noncomputable def AprimeZW
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : SuTwo :=
  -RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))

/-- `A′(w,x) = A(w,x) = -A(x,w)` (antisymmetry; the STORED bond is `(x,w)`). -/
noncomputable def AprimeWX (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : SuTwo :=
  -A (p.1, p.2.1.2)

/-- **`(D_U^1 A)(p) = Σ_{b⊂∂(p)_z} A′(b) = curlValueCovariant U A p`** — `D_U^1` is `η=1` of the
tree's own `curlValueCovariant`, not a new operator (`DELTA_PRIME.md`'s finding, re-derived here
independently by summing the four `A′` components term-by-term against `curlValueCovariant`'s own
definition). -/
theorem sum_Aprime_eq_curl
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    AprimeXY A p + AprimeYZ U A p + AprimeZW U A p + AprimeWX A p = curlValueCovariant U A p := by
  unfold AprimeXY AprimeYZ AprimeZW AprimeWX curlValueCovariant
  abel

#print axioms sum_Aprime_eq_curl

/-! ## §3 — the commutator sum, and the two real-valued terms of `Δ′` -/

/-- **`Σ_{b1≺b2⊂∂(p)_z} i[A′(b1),A′(b2)]`**, the 6 ordered pairs of `{A′_1,A′_2,A′_3,A′_4} =
{A′(z,w),A′(w,x),A′(x,y),A′(y,z)}` under the `≺`-order read off p.390 (module docstring). A
`2×2` complex matrix (commutators of `𝔰𝔲(2)`-valued matrices are again skew-Hermitian, so `i·[,]`
is Hermitian — consistent with the term needing to pair against the Hermitian `Im U(∂p)` factor
under a single trace). -/
noncomputable def commutatorMatrixSum
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : Matrix (Fin 2) (Fin 2) ℂ :=
  let a1 : Matrix (Fin 2) (Fin 2) ℂ := (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ)
  let a2 : Matrix (Fin 2) (Fin 2) ℂ := (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ)
  let a3 : Matrix (Fin 2) (Fin 2) ℂ := (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ)
  let a4 : Matrix (Fin 2) (Fin 2) ℂ := (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ)
  Complex.I •
    ((a1 * a2 - a2 * a1) + (a1 * a3 - a3 * a1) + (a1 * a4 - a4 * a1) +
      (a2 * a3 - a3 * a2) + (a2 * a4 - a4 * a2) + (a3 * a4 - a4 * a3))

/-- **CMP99b (3.10)'s FIRST `Δ′` term, per plaquette**: `tr((D_U^1A)(p))²(Re U(∂p) - 1)`, a single
trace over the three-factor matrix product (forced by scalar well-definedness and confirmed by
eq. 3.7's parallel derivation, `DELTA_PRIME.md`), real part taken (the underlying quantity is real
for a hermitian quadratic form; see the module docstring's "Convention inherited" note for the
sign-transport question this `.re` does NOT resolve). -/
noncomputable def deltaPrimeFirstTerm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  (Matrix.trace
      ((curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ) *
          (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ) *
        (reHolonomy U p - 1))).re

/-- **CMP99b (3.10)'s SECOND `Δ′` term, per plaquette**: `tr(Σ i[A′(b1),A′(b2)] · Im U(∂p))`. -/
noncomputable def deltaPrimeSecondTerm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  (Matrix.trace (commutatorMatrixSum U A p * imHolonomy U p)).re

/-- The full per-plaquette summand of `Δ′`. -/
noncomputable def deltaPrimePlaqTerm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  deltaPrimeFirstTerm U A p + deltaPrimeSecondTerm U A p

/-- **`⟨A,Δ′A⟩`**, CMP99b (3.10)'s full second term of `Δ`, summed over all plaquettes. -/
noncomputable def deltaPrimeQuadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, deltaPrimePlaqTerm U A p

/-! ## §4 — THE ASSEMBLY: CMP99b eq. (3.10) itself, `⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ′A⟩` -/

/-- ## ⚠ WRONG-SIGN ASSEMBLY — DO NOT CONSUME AS CMP99b (3.10). Use `deltaQuadFormFaithful` below.
**Finding F3, 2026-07-22, third-family (Kimi K3) gate — `compute/kimi_sign_gate/KIMI_SIGN_GATE.md`,
re-derived COLD from its own 300 dpi renders of CMP99b pp.390-392, printed headers verified.**

The definition below assembles `dstarDQuadForm + deltaPrimeQuadForm` (UNTRANSPORTED `Δ′`). **That is
the wrong sign under this tree's own conventions**, and the docstring on `deltaQuadForm_eq` calling
it *"Eq. (3.10) itself, as a theorem"* is therefore false as a faithfulness claim.

**Why (the requirement is forced, not stylistic).** The tree's carrier `suTwo` is ANTI-Hermitian
(`Xᴴ = -X`), while CMP99b p.391 states its fields are *"N × N **hermitian** matrices"* with
`U′ = exp(iηA)` and normalized trace `tr 1 = 1`. The two presentations are related by `φ : X ↦ iX`.
Faithfulness therefore requires `Q_tree(X) = Q_paper(iX)`, and under `A = iX`:
* `⟨A,D*DA⟩` — built here from `hsInner`, which IS the `φ`-transport
  (`φ(X)·φ(Y) = tr((iX)(iY)) = −tr(XY) = −½Tr(XY) = hsInner X Y`), so **the correction is already
  inherited**;
* both `Δ′` terms are homogeneous quadratic in `A` and built from RAW `Matrix.trace`, so raw
  substitution `A = iX` contributes `i² = −1` and **flips their sign** — the correction is NOT
  inherited.

Hence the faithful assembly is `dstarDQuadForm + deltaPrimeQuadFormTransported`, i.e. in this file's
untransported convention **`Δ = D*D − Δ′`**. The discrepancy is real and measured, not notional:
`8` vs `−8` on the `Δ′` piece at the `witnessU`/`deltaWitnessConfig` witness (`:854` vs `:1068`),
whose background is proved NON-CENTRAL, with both readings agreeing at `0` on the trivial control.

Note (3.10) itself prints a PLUS between the two terms — the sign flip lives entirely in the
carrier convention, not in the paper.

**Retained, not deleted, for provenance and because downstream theorems reference it.** -/
noncomputable def deltaQuadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  dstarDQuadForm U A + deltaPrimeQuadForm U A

/-- **Eq. (3.10) itself, as a theorem**: the assembly is definitionally the sum of the two named
terms — stated explicitly so a reader does not have to reconstruct it from `deltaQuadForm`'s
`unfold`. -/
theorem deltaQuadForm_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaQuadForm U A = dstarDQuadForm U A + deltaPrimeQuadForm U A := rfl

#print axioms deltaQuadForm_eq

/-! ## §5 — `Δ′` VANISHES at the trivial background, for ANY field `A` (mandate property 3)

CMP99b, immediately after eq. (3.10) (`DELTA_PRIME.md`, VERBATIM): "we have written it this way
because with our assumptions on the configuration `U` the operator `Δ′` will be a bounded, small
operator, which will be treated as a small perturbation of `D*D`." At the trivial background
(`U ≡ 1` on every bond) the holonomy of EVERY plaquette is `1`, so `Re U(∂p) = 1` (killing the
first term's `(Re U(∂p) - 1)` factor identically) and `Im U(∂p) = 0` (killing the second term's
`Im U(∂p)` factor identically) — a fully GENERAL fact, independent of `A` and of the lattice `L`,
needing no witness/enumeration at all. -/

/-- The trivial (all-identity) link configuration, on ANY periodic lattice `L`. -/
noncomputable def trivialU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L := fun _ => 1

theorem periodicPlaquetteHolonomy_trivialU (p : PeriodicLatticePlaquette L) :
    periodicPlaquetteHolonomy (trivialU (L := L)) p = 1 := by
  unfold periodicPlaquetteHolonomy trivialU
  simp

theorem holonomyElem_trivialU (p : PeriodicLatticePlaquette L) :
    holonomyElem (trivialU (L := L)) p = 1 := by
  unfold holonomyElem
  exact periodicPlaquetteHolonomy_trivialU p

theorem holonomyElemInv_trivialU (p : PeriodicLatticePlaquette L) :
    holonomyElemInv (trivialU (L := L)) p = 1 := by
  unfold holonomyElemInv
  rw [holonomyElem_trivialU]
  simp

theorem reHolonomy_trivialU (p : PeriodicLatticePlaquette L) :
    reHolonomy (trivialU (L := L)) p = 1 := by
  unfold reHolonomy
  simp only [holonomyElem_trivialU, holonomyElemInv_trivialU]
  simp
  module

theorem imHolonomy_trivialU (p : PeriodicLatticePlaquette L) :
    imHolonomy (trivialU (L := L)) p = 0 := by
  unfold imHolonomy
  simp only [holonomyElem_trivialU, holonomyElemInv_trivialU]
  simp

#print axioms periodicPlaquetteHolonomy_trivialU
#print axioms reHolonomy_trivialU
#print axioms imHolonomy_trivialU

/-- **`Δ′` vanishes pointwise (per plaquette) at the trivial background, for ANY `A`.** -/
theorem deltaPrimePlaqTerm_trivialU (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    deltaPrimePlaqTerm (trivialU (L := L)) A p = 0 := by
  unfold deltaPrimePlaqTerm deltaPrimeFirstTerm deltaPrimeSecondTerm
  rw [reHolonomy_trivialU, imHolonomy_trivialU]
  simp

#print axioms deltaPrimePlaqTerm_trivialU

/-- **MANDATE PROPERTY 3, fully general**: `Δ′` vanishes at the trivial background, for ANY field
`A` and ANY periodic lattice `L` — not merely on a witness. -/
theorem deltaPrimeQuadForm_vanishes_at_trivial (A : Bond L → SuTwo) :
    deltaPrimeQuadForm (trivialU (L := L)) A = 0 := by
  unfold deltaPrimeQuadForm
  exact Finset.sum_eq_zero (fun p _ => deltaPrimePlaqTerm_trivialU A p)

#print axioms deltaPrimeQuadForm_vanishes_at_trivial

/-- **§S91 degenerate-inhabitation check**: the vanishing above is NOT secretly a statement about
the ZERO field — it holds for the `Nonempty`/witness-style DEGENERATE choice `A := 0` trivially
(as a sanity check that the statement is not vacuous in the wrong direction), but ALSO, and this
is the substance, for the FULLY GENERAL `A` quantified above (no restriction on `A` was smuggled
into `deltaPrimeQuadForm_vanishes_at_trivial`'s hypothesis list — its ONLY hypothesis is `A`
itself, universally quantified). -/
theorem deltaPrimeQuadForm_vanishes_at_trivial_zero_instance :
    deltaPrimeQuadForm (trivialU (L := AdmissibleSubspace.witnessL)) (0 : Bond _ → SuTwo) = 0 :=
  deltaPrimeQuadForm_vanishes_at_trivial 0

#print axioms deltaPrimeQuadForm_vanishes_at_trivial_zero_instance

/-! ## §6 — `Δ′` is genuinely `U`-dependent AND nonzero (mandate properties 1/2), on a concrete
single-bond witness on `AdmissibleSubspace.witnessL`, against `CovariantOperators.witnessU`
(REUSED, LAW-19: nontrivial only on the bond `(witnessY,0)`, `witnessMElem` there, identity
elsewhere).

A bond of direction `0` can appear in a plaquette's four `curlValueCovariant` boundary-bond reads
in exactly two ways (`plaquette_snd_dir_ne_zero`, reused from `CovariantHj`, rules out the other
two): as the DIRECT "`T1`" read `(p.1,p.2.1.1)` when `p.1=witnessY ∧ p.2.1.1=0` — exactly
`witnessPlaquette`/`myWitnessPlaquette2` (`eq_witnessPlaquette_or_myWitnessPlaquette2`, REUSED) —
or as the "`T3`" read `(shift_{p.2.1.2}p.1, p.2.1.1)` when `shift_ν(p.1)=witnessY ∧ p.2.1.1=0` for
`ν∈{1,2}` — two NEW plaquettes, `p3`/`p4` below, based at the two predecessors of `witnessY` in
directions `1`/`2`. -/

/-- Predecessor of `witnessY` in direction `1` (`3 = -1` in `Fin 4`, so `shift_1` of this site
returns to `witnessY`, proved below). -/
def p3Site : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  Function.update AdmissibleSubspace.witnessY 1 3

/-- Predecessor of `witnessY` in direction `2`. -/
def p4Site : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  Function.update AdmissibleSubspace.witnessY 2 3

theorem shift_p3Site_eq :
    periodicLatticeShift p3Site 1 = AdmissibleSubspace.witnessY := by decide

theorem shift_p4Site_eq :
    periodicLatticeShift p4Site 2 = AdmissibleSubspace.witnessY := by decide

theorem p3Site_ne_witnessY : p3Site ≠ AdmissibleSubspace.witnessY := by decide

theorem p4Site_ne_witnessY : p4Site ≠ AdmissibleSubspace.witnessY := by decide

/-- The third exceptional plaquette: based at `p3Site`, directions `(0,1)`. -/
def p3 : PeriodicLatticePlaquette AdmissibleSubspace.witnessL := (p3Site, ⟨(0, 1), by decide⟩)

/-- The fourth exceptional plaquette: based at `p4Site`, directions `(0,2)`. -/
def p4 : PeriodicLatticePlaquette AdmissibleSubspace.witnessL := (p4Site, ⟨(0, 2), by decide⟩)

/-- **`periodicLatticeShift` is injective in its site argument, for any fixed direction`**` — the
general fact making `p3`/`p4` the UNIQUE plaquettes reading bond `(witnessY,0)` in "T3" position.
Not present anywhere else in the tree (checked); a clean, reusable, general lemma. -/
theorem periodicLatticeShift_injective {μ : Fin 3} {x y : PeriodicLatticeSite L}
    (h : periodicLatticeShift x μ = periodicLatticeShift y μ) : x = y := by
  funext ρ
  by_cases hρ : ρ = μ
  · subst hρ
    have hx := congrFun h ρ
    simp only [periodicLatticeShift, Function.update_self] at hx
    exact add_right_cancel hx
  · have hx := congrFun h ρ
    simp only [periodicLatticeShift, Function.update_of_ne hρ] at hx
    exact hx

#print axioms periodicLatticeShift_injective

/-- **Uniqueness of `p3`/`p4`** — the "T3" analog of
`eq_witnessPlaquette_or_myWitnessPlaquette2`. -/
theorem eq_p3_or_p4 {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (h1 : periodicLatticeShift p.1 p.2.1.2 = AdmissibleSubspace.witnessY)
    (h2 : p.2.1.1 = (0 : Fin 3)) : p = p3 ∨ p = p4 := by
  have hlt := p.2.2
  rw [h2] at hlt
  have hval : p.2.1.2.val = 1 ∨ p.2.1.2.val = 2 := by
    have h3 : p.2.1.2.val < 3 := p.2.1.2.isLt
    have h4 : 0 < p.2.1.2.val := hlt
    omega
  rcases hval with hval | hval
  · left
    have h3 : p.2.1.2 = (1 : Fin 3) := Fin.ext hval
    rw [h3] at h1
    have hp1 : p.1 = p3Site := periodicLatticeShift_injective (h1.trans shift_p3Site_eq.symm)
    have hpair : p.2.1 = ((0 : Fin 3), (1 : Fin 3)) := Prod.ext h2 h3
    have hsub : p.2 = p3.2 := Subtype.ext hpair
    exact Prod.ext hp1 hsub
  · right
    have h3 : p.2.1.2 = (2 : Fin 3) := Fin.ext hval
    rw [h3] at h1
    have hp1 : p.1 = p4Site := periodicLatticeShift_injective (h1.trans shift_p4Site_eq.symm)
    have hpair : p.2.1 = ((0 : Fin 3), (2 : Fin 3)) := Prod.ext h2 h3
    have hsub : p.2 = p4.2 := Subtype.ext hpair
    exact Prod.ext hp1 hsub

#print axioms eq_p3_or_p4

/-- **The single-bond witness field**: `suTwoWitness` on `(witnessY,0)` alone, `0` elsewhere. -/
noncomputable def deltaWitnessConfig : Bond AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then suTwoWitness else 0

theorem deltaWitnessConfig_at_e0 :
    deltaWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) = suTwoWitness := by
  simp [deltaWitnessConfig]

theorem deltaWitnessConfig_elsewhere {e : Bond AdmissibleSubspace.witnessL}
    (h : e ≠ (AdmissibleSubspace.witnessY, (0 : Fin 3))) : deltaWitnessConfig e = 0 := by
  simp [deltaWitnessConfig, h]

/-- **General vanishing lemma**: if a config is `0` on ALL FOUR of a plaquette's boundary bonds,
`Δ′`'s per-plaquette term there is `0` REGARDLESS of `U` (`curlValueCovariant`/every `A′_i` reduce
to `RMap _ 0 = 0` or `0` directly by linearity; no cancellation, no holonomy computation needed). -/
theorem deltaPrimePlaqTerm_eq_zero_of_bonds_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h1 : A (p.1, p.2.1.1) = 0) (h2 : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0)
    (h3 : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) (h4 : A (p.1, p.2.1.2) = 0) :
    deltaPrimePlaqTerm U A p = 0 := by
  have hcurl : curlValueCovariant U A p = 0 := by
    unfold curlValueCovariant
    rw [h1, h2, h3, h4]
    simp
  have hA1 : AprimeZW U A p = 0 := by unfold AprimeZW; rw [h3]; simp
  have hA2 : AprimeWX A p = 0 := by unfold AprimeWX; rw [h4]; simp
  have hA3 : AprimeXY A p = 0 := by unfold AprimeXY; rw [h1]
  have hA4 : AprimeYZ U A p = 0 := by unfold AprimeYZ; rw [h2]; simp
  unfold deltaPrimePlaqTerm deltaPrimeFirstTerm deltaPrimeSecondTerm
  rw [hcurl]
  have hcomm : commutatorMatrixSum U A p = 0 := by
    unfold commutatorMatrixSum
    simp only [hA1, hA2, hA3, hA4]
    norm_num
  rw [hcomm]
  norm_num

#print axioms deltaPrimePlaqTerm_eq_zero_of_bonds_zero

/-- **The forward-direction vanishing at every plaquette OUTSIDE the 4 exceptional ones**, for
`deltaWitnessConfig` (any `U`). -/
theorem deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL)
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    deltaPrimePlaqTerm U deltaWitnessConfig p = 0 := by
  apply deltaPrimePlaqTerm_eq_zero_of_bonds_zero
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp1 h
    · exact hp2 h
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact hp3 h
    · exact hp4 h
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)

#print axioms deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero

/-! ## §7 — holonomy of `witnessU` at the 4 exceptional plaquettes: `witnessMElem` (at
`witnessPlaquette`/`myWitnessPlaquette2`, both `T1`-slot reads) or `witnessMElem⁻¹` (at `p3`/`p4`,
both `T3`-slot reads, the special bond appearing INVERTED in the `(U(shift_ν x,μ))⁻¹` factor). -/

theorem witnessU_at_y_nu2 :
    witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_w_mu2 :
    witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_x_nu2 : witnessU (AdmissibleSubspace.witnessY, (2 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_p3Site_mu : witnessU (p3Site, (0 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_p3Site_shift0_nu :
    witnessU (periodicLatticeShift p3Site 0, (1 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_p3Site_nu : witnessU (p3Site, (1 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_p4Site_mu : witnessU (p4Site, (0 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_p4Site_shift0_nu :
    witnessU (periodicLatticeShift p4Site 0, (2 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem witnessU_at_p4Site_nu : witnessU (p4Site, (2 : Fin 3)) = 1 := by
  unfold witnessU; rw [if_neg (by decide)]

theorem holonomy_witnessU_witnessPlaquette :
    holonomyElem witnessU witnessPlaquette = witnessMElem := by
  show witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
      witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)) *
      (witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)))⁻¹ *
      (witnessU (AdmissibleSubspace.witnessY, (1 : Fin 3)))⁻¹ = witnessMElem
  rw [witnessU_at_x_mu, witnessU_at_y_nu, witnessU_at_w_mu, witnessU_at_x_nu]
  simp

theorem holonomy_witnessU_myWitnessPlaquette2 :
    holonomyElem witnessU myWitnessPlaquette2 = witnessMElem := by
  show witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
      witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3)) *
      (witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3)))⁻¹ *
      (witnessU (AdmissibleSubspace.witnessY, (2 : Fin 3)))⁻¹ = witnessMElem
  rw [witnessU_at_x_mu, witnessU_at_y_nu2, witnessU_at_w_mu2, witnessU_at_x_nu2]
  simp

theorem holonomy_witnessU_p3 : holonomyElem witnessU p3 = witnessMElem⁻¹ := by
  show witnessU (p3Site, (0 : Fin 3)) *
      witnessU (periodicLatticeShift p3Site 0, (1 : Fin 3)) *
      (witnessU (periodicLatticeShift p3Site 1, (0 : Fin 3)))⁻¹ *
      (witnessU (p3Site, (1 : Fin 3)))⁻¹ = witnessMElem⁻¹
  rw [witnessU_at_p3Site_mu, witnessU_at_p3Site_shift0_nu, shift_p3Site_eq, witnessU_at_x_mu,
    witnessU_at_p3Site_nu]
  simp

theorem holonomy_witnessU_p4 : holonomyElem witnessU p4 = witnessMElem⁻¹ := by
  show witnessU (p4Site, (0 : Fin 3)) *
      witnessU (periodicLatticeShift p4Site 0, (2 : Fin 3)) *
      (witnessU (periodicLatticeShift p4Site 2, (0 : Fin 3)))⁻¹ *
      (witnessU (p4Site, (2 : Fin 3)))⁻¹ = witnessMElem⁻¹
  rw [witnessU_at_p4Site_mu, witnessU_at_p4Site_shift0_nu, shift_p4Site_eq, witnessU_at_x_mu,
    witnessU_at_p4Site_nu]
  simp

theorem holonomyElemInv_witnessU_witnessPlaquette :
    holonomyElemInv witnessU witnessPlaquette = witnessMElem⁻¹ := by
  unfold holonomyElemInv; rw [holonomy_witnessU_witnessPlaquette]

theorem holonomyElemInv_witnessU_myWitnessPlaquette2 :
    holonomyElemInv witnessU myWitnessPlaquette2 = witnessMElem⁻¹ := by
  unfold holonomyElemInv; rw [holonomy_witnessU_myWitnessPlaquette2]

theorem holonomyElemInv_witnessU_p3 : holonomyElemInv witnessU p3 = witnessMElem := by
  unfold holonomyElemInv; rw [holonomy_witnessU_p3, inv_inv]

theorem holonomyElemInv_witnessU_p4 : holonomyElemInv witnessU p4 = witnessMElem := by
  unfold holonomyElemInv; rw [holonomy_witnessU_p4, inv_inv]

#print axioms holonomy_witnessU_witnessPlaquette
#print axioms holonomy_witnessU_myWitnessPlaquette2
#print axioms holonomy_witnessU_p3
#print axioms holonomy_witnessU_p4
#print axioms holonomyElemInv_witnessU_witnessPlaquette
#print axioms holonomyElemInv_witnessU_myWitnessPlaquette2
#print axioms holonomyElemInv_witnessU_p3
#print axioms holonomyElemInv_witnessU_p4

/-- **`(witnessMElem⁻¹ : Matrix) = (witnessMElem : Matrix)ᴴ`** — the group inverse on
`specialUnitaryGroup` is `star`, which on complex matrices is `conjTranspose`
(`Matrix.specialUnitaryGroup.star_eq_inv`/`.coe_star`, `Matrix.star_eq_conjTranspose`). -/
theorem witnessMElem_inv_coe_eq_conjTranspose :
    ((witnessMElem⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, Matrix.star_eq_conjTranspose]

/-- **`witnessM + witnessMᴴ = 0`** — the concrete `2×2` fact making `Re(witnessMElem) = 0`
(hand-verified independently, `compute` scratchpad's numpy check, `witnessM=!![0,1;-1,0]`,
`witnessMᴴ=!![0,-1;1,0]`). -/
theorem witnessMElem_coe_add_inv_coe_eq_zero :
    (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) +
      ((witnessMElem⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  rw [witnessMElem_inv_coe_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessMElem, witnessM, Matrix.conjTranspose_apply]

#print axioms witnessMElem_inv_coe_eq_conjTranspose
#print axioms witnessMElem_coe_add_inv_coe_eq_zero

/-- **`Re U(∂p) = 0` at ALL FOUR exceptional plaquettes** — the holonomy is either `witnessMElem`
or its inverse there, and `Re` is symmetric in `g,g⁻¹` (`reHolonomy`'s own `hol+hol⁻¹` shape), so
both cases reduce to the SAME matrix fact. -/
theorem reHolonomy_witnessU_witnessPlaquette : reHolonomy witnessU witnessPlaquette = 0 := by
  unfold reHolonomy
  rw [holonomy_witnessU_witnessPlaquette, holonomyElemInv_witnessU_witnessPlaquette,
    witnessMElem_coe_add_inv_coe_eq_zero]
  module

theorem reHolonomy_witnessU_myWitnessPlaquette2 :
    reHolonomy witnessU myWitnessPlaquette2 = 0 := by
  unfold reHolonomy
  rw [holonomy_witnessU_myWitnessPlaquette2, holonomyElemInv_witnessU_myWitnessPlaquette2,
    witnessMElem_coe_add_inv_coe_eq_zero]
  module

theorem reHolonomy_witnessU_p3 : reHolonomy witnessU p3 = 0 := by
  unfold reHolonomy
  rw [holonomy_witnessU_p3, holonomyElemInv_witnessU_p3, add_comm,
    witnessMElem_coe_add_inv_coe_eq_zero]
  module

theorem reHolonomy_witnessU_p4 : reHolonomy witnessU p4 = 0 := by
  unfold reHolonomy
  rw [holonomy_witnessU_p4, holonomyElemInv_witnessU_p4, add_comm,
    witnessMElem_coe_add_inv_coe_eq_zero]
  module

#print axioms reHolonomy_witnessU_witnessPlaquette
#print axioms reHolonomy_witnessU_myWitnessPlaquette2
#print axioms reHolonomy_witnessU_p3
#print axioms reHolonomy_witnessU_p4

/-! ## §8 — the covariant curl of `deltaWitnessConfig` at the 4 exceptional plaquettes, and the
per-plaquette `Δ′` terms, under `witnessU`. -/

theorem curl_witnessU_witnessPlaquette :
    curlValueCovariant witnessU deltaWitnessConfig witnessPlaquette = suTwoWitness := by
  show deltaWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))) -
      RMap (witnessU (AdmissibleSubspace.witnessY, (1 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))) -
      deltaWitnessConfig (AdmissibleSubspace.witnessY, (1 : Fin 3)) = suTwoWitness
  rw [deltaWitnessConfig_at_e0, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp

theorem curl_witnessU_myWitnessPlaquette2 :
    curlValueCovariant witnessU deltaWitnessConfig myWitnessPlaquette2 = suTwoWitness := by
  show deltaWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3))) -
      RMap (witnessU (AdmissibleSubspace.witnessY, (2 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3))) -
      deltaWitnessConfig (AdmissibleSubspace.witnessY, (2 : Fin 3)) = suTwoWitness
  rw [deltaWitnessConfig_at_e0, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp

theorem curl_witnessU_p3 :
    curlValueCovariant witnessU deltaWitnessConfig p3 = -suTwoWitness := by
  show deltaWitnessConfig (p3Site, (0 : Fin 3)) +
      RMap (witnessU (p3Site, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p3Site 0, (1 : Fin 3))) -
      RMap (witnessU (p3Site, (1 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p3Site 1, (0 : Fin 3))) -
      deltaWitnessConfig (p3Site, (1 : Fin 3)) = -suTwoWitness
  rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), shift_p3Site_eq, deltaWitnessConfig_at_e0,
    witnessU_at_p3Site_nu, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp [RMap_one]

theorem curl_witnessU_p4 :
    curlValueCovariant witnessU deltaWitnessConfig p4 = -suTwoWitness := by
  show deltaWitnessConfig (p4Site, (0 : Fin 3)) +
      RMap (witnessU (p4Site, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p4Site 0, (2 : Fin 3))) -
      RMap (witnessU (p4Site, (2 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p4Site 2, (0 : Fin 3))) -
      deltaWitnessConfig (p4Site, (2 : Fin 3)) = -suTwoWitness
  rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), shift_p4Site_eq, deltaWitnessConfig_at_e0,
    witnessU_at_p4Site_nu, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp [RMap_one]

#print axioms curl_witnessU_witnessPlaquette
#print axioms curl_witnessU_myWitnessPlaquette2
#print axioms curl_witnessU_p3
#print axioms curl_witnessU_p4

/-! ## §9 — the two `Δ′` sub-terms at the 4 exceptional plaquettes: FIRST term `= 2` everywhere
(`X² = -1` regardless of `X`'s sign, `Y = 0 - 1 = -1`, `tr((-1)(-1)) = tr(1) = 2`); SECOND term
`= 0` everywhere (only ONE of the four `A′_i` is nonzero at each of these plaquettes, so every one
of the 6 commutator terms has a zero factor). -/

theorem suTwoWitness_coe_sq :
    (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) * (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  show suTwoWitnessVal * suTwoWitnessVal = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoWitnessVal, Matrix.mul_apply, Fin.sum_univ_two]

theorem negSuTwoWitness_coe_sq :
    (-suTwoWitness : SuTwo).val * (-suTwoWitness : SuTwo).val =
      (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : ((-suTwoWitness : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) =
      -(suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [this, neg_mul_neg, suTwoWitness_coe_sq]

theorem deltaPrimeFirstTerm_witnessU_witnessPlaquette :
    deltaPrimeFirstTerm witnessU deltaWitnessConfig witnessPlaquette = 2 := by
  unfold deltaPrimeFirstTerm
  rw [curl_witnessU_witnessPlaquette, reHolonomy_witnessU_witnessPlaquette, suTwoWitness_coe_sq]
  norm_num [Matrix.trace_fin_two]

theorem deltaPrimeFirstTerm_witnessU_myWitnessPlaquette2 :
    deltaPrimeFirstTerm witnessU deltaWitnessConfig myWitnessPlaquette2 = 2 := by
  unfold deltaPrimeFirstTerm
  rw [curl_witnessU_myWitnessPlaquette2, reHolonomy_witnessU_myWitnessPlaquette2,
    suTwoWitness_coe_sq]
  norm_num [Matrix.trace_fin_two]

theorem deltaPrimeFirstTerm_witnessU_p3 :
    deltaPrimeFirstTerm witnessU deltaWitnessConfig p3 = 2 := by
  unfold deltaPrimeFirstTerm
  rw [curl_witnessU_p3, reHolonomy_witnessU_p3, negSuTwoWitness_coe_sq]
  norm_num [Matrix.trace_fin_two]

theorem deltaPrimeFirstTerm_witnessU_p4 :
    deltaPrimeFirstTerm witnessU deltaWitnessConfig p4 = 2 := by
  unfold deltaPrimeFirstTerm
  rw [curl_witnessU_p4, reHolonomy_witnessU_p4, negSuTwoWitness_coe_sq]
  norm_num [Matrix.trace_fin_two]

#print axioms suTwoWitness_coe_sq
#print axioms negSuTwoWitness_coe_sq
#print axioms deltaPrimeFirstTerm_witnessU_witnessPlaquette
#print axioms deltaPrimeFirstTerm_witnessU_myWitnessPlaquette2
#print axioms deltaPrimeFirstTerm_witnessU_p3
#print axioms deltaPrimeFirstTerm_witnessU_p4

/-- **If `A′_1,A′_2,A′_4` (all but `A′_3`) are `0`, the commutator sum is `0`** — every one of the
6 ordered pairs includes at least one index from `{1,2,4}` (the pairs are `(1,2),(1,3),(1,4),
(2,3),(2,4),(3,4)`; no pair avoids `{1,2,4}` entirely since that would need two DISTINCT indices
both equal to `3`). -/
theorem commutatorMatrixSum_eq_zero_of_a1a2a4_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h1 : (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h2 : (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h4 : (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) = 0) :
    commutatorMatrixSum U A p = 0 := by
  unfold commutatorMatrixSum
  simp only [h1, h2, h4]
  norm_num

/-- **If `A′_2,A′_3,A′_4` (all but `A′_1`) are `0`, the commutator sum is `0`** — symmetric
argument, every pair includes at least one index from `{2,3,4}`. -/
theorem commutatorMatrixSum_eq_zero_of_a2a3a4_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h2 : (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h3 : (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h4 : (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) = 0) :
    commutatorMatrixSum U A p = 0 := by
  unfold commutatorMatrixSum
  simp only [h2, h3, h4]
  norm_num

#print axioms commutatorMatrixSum_eq_zero_of_a1a2a4_zero
#print axioms commutatorMatrixSum_eq_zero_of_a2a3a4_zero

theorem deltaPrimeSecondTerm_witnessU_witnessPlaquette :
    deltaPrimeSecondTerm witnessU deltaWitnessConfig witnessPlaquette = 0 := by
  unfold deltaPrimeSecondTerm
  have h1 : (AprimeZW witnessU deltaWitnessConfig witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeZW
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h2 : (AprimeWX deltaWitnessConfig witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h4 : (AprimeYZ witnessU deltaWitnessConfig witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  rw [commutatorMatrixSum_eq_zero_of_a1a2a4_zero _ _ _ h1 h2 h4]
  simp

theorem deltaPrimeSecondTerm_witnessU_myWitnessPlaquette2 :
    deltaPrimeSecondTerm witnessU deltaWitnessConfig myWitnessPlaquette2 = 0 := by
  unfold deltaPrimeSecondTerm
  have h1 : (AprimeZW witnessU deltaWitnessConfig myWitnessPlaquette2 :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeZW
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h2 : (AprimeWX deltaWitnessConfig myWitnessPlaquette2 :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h4 : (AprimeYZ witnessU deltaWitnessConfig myWitnessPlaquette2 :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  rw [commutatorMatrixSum_eq_zero_of_a1a2a4_zero _ _ _ h1 h2 h4]
  simp

theorem deltaPrimeSecondTerm_witnessU_p3 :
    deltaPrimeSecondTerm witnessU deltaWitnessConfig p3 = 0 := by
  unfold deltaPrimeSecondTerm
  have h2 : (AprimeWX deltaWitnessConfig p3 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h3 : (AprimeXY deltaWitnessConfig p3 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeXY
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h4 : (AprimeYZ witnessU deltaWitnessConfig p3 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  rw [commutatorMatrixSum_eq_zero_of_a2a3a4_zero _ _ _ h2 h3 h4]
  simp

theorem deltaPrimeSecondTerm_witnessU_p4 :
    deltaPrimeSecondTerm witnessU deltaWitnessConfig p4 = 0 := by
  unfold deltaPrimeSecondTerm
  have h2 : (AprimeWX deltaWitnessConfig p4 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h3 : (AprimeXY deltaWitnessConfig p4 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeXY
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  have h4 : (AprimeYZ witnessU deltaWitnessConfig p4 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ
    rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
    simp
  rw [commutatorMatrixSum_eq_zero_of_a2a3a4_zero _ _ _ h2 h3 h4]
  simp

#print axioms deltaPrimeSecondTerm_witnessU_witnessPlaquette
#print axioms deltaPrimeSecondTerm_witnessU_myWitnessPlaquette2
#print axioms deltaPrimeSecondTerm_witnessU_p3
#print axioms deltaPrimeSecondTerm_witnessU_p4

/-- **`deltaPrimePlaqTerm = 2` at all 4 exceptional plaquettes.** -/
theorem deltaPrimePlaqTerm_witnessU_witnessPlaquette :
    deltaPrimePlaqTerm witnessU deltaWitnessConfig witnessPlaquette = 2 := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_witnessU_witnessPlaquette,
    deltaPrimeSecondTerm_witnessU_witnessPlaquette]
  norm_num

theorem deltaPrimePlaqTerm_witnessU_myWitnessPlaquette2 :
    deltaPrimePlaqTerm witnessU deltaWitnessConfig myWitnessPlaquette2 = 2 := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_witnessU_myWitnessPlaquette2,
    deltaPrimeSecondTerm_witnessU_myWitnessPlaquette2]
  norm_num

theorem deltaPrimePlaqTerm_witnessU_p3 :
    deltaPrimePlaqTerm witnessU deltaWitnessConfig p3 = 2 := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_witnessU_p3, deltaPrimeSecondTerm_witnessU_p3]
  norm_num

theorem deltaPrimePlaqTerm_witnessU_p4 :
    deltaPrimePlaqTerm witnessU deltaWitnessConfig p4 = 2 := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_witnessU_p4, deltaPrimeSecondTerm_witnessU_p4]
  norm_num

#print axioms deltaPrimePlaqTerm_witnessU_witnessPlaquette
#print axioms deltaPrimePlaqTerm_witnessU_myWitnessPlaquette2
#print axioms deltaPrimePlaqTerm_witnessU_p3
#print axioms deltaPrimePlaqTerm_witnessU_p4

/-! ## §10 — THE ASSEMBLY: `deltaPrimeQuadForm witnessU deltaWitnessConfig = 8`, and the three
mandate properties. -/

/-- **The full lattice sum reduces to the 4-element exceptional set** — every other plaquette
contributes `0` (`deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero`), and the 4 exceptional
plaquettes contribute `2` each. -/
theorem deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq :
    deltaPrimeQuadForm witnessU deltaWitnessConfig = 8 := by
  unfold deltaPrimeQuadForm
  have hS : ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hzero : ∀ p ∈ (Finset.univ :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)),
      p ∉ ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
        Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) →
      deltaPrimePlaqTerm witnessU deltaWitnessConfig p = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    exact deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero witnessU hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  rw [← Finset.sum_subset hS hzero]
  have hne1 : witnessPlaquette ≠ myWitnessPlaquette2 := by decide
  have hne2 : witnessPlaquette ≠ p3 := by decide
  have hne3 : witnessPlaquette ≠ p4 := by decide
  have hne4 : myWitnessPlaquette2 ≠ p3 := by decide
  have hne5 : myWitnessPlaquette2 ≠ p4 := by decide
  have hne6 : p3 ≠ p4 := by decide
  rw [Finset.sum_insert (by simp [hne1, hne2, hne3]),
    Finset.sum_insert (by simp [hne4, hne5]), Finset.sum_pair hne6,
    deltaPrimePlaqTerm_witnessU_witnessPlaquette, deltaPrimePlaqTerm_witnessU_myWitnessPlaquette2,
    deltaPrimePlaqTerm_witnessU_p3, deltaPrimePlaqTerm_witnessU_p4]
  norm_num

#print axioms deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq

/-- **MANDATE PROPERTY 2 — `Δ′` is nonzero on a concrete configuration.** -/
theorem deltaPrimeQuadForm_witnessU_ne_zero :
    deltaPrimeQuadForm witnessU deltaWitnessConfig ≠ 0 := by
  rw [deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq]
  norm_num

/-- **MANDATE PROPERTY 1 — `Δ′` is genuinely `U`-dependent**: `0` at the trivial background
(§5, fully general) vs `8` at `witnessU`, on the SAME field `deltaWitnessConfig`. -/
theorem deltaPrimeQuadForm_genuinely_U_dependent :
    deltaPrimeQuadForm (trivialU (L := AdmissibleSubspace.witnessL)) deltaWitnessConfig ≠
      deltaPrimeQuadForm witnessU deltaWitnessConfig := by
  rw [deltaPrimeQuadForm_vanishes_at_trivial, deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq]
  norm_num

#print axioms deltaPrimeQuadForm_witnessU_ne_zero
#print axioms deltaPrimeQuadForm_genuinely_U_dependent

/-- **The FULL `Δ = D*D + Δ′` (eq. 3.10) is ALSO genuinely `U`-dependent** on this witness —
assembled from `Δ′`'s own `U`-dependence above (this is `Δ′`'s contribution alone; `dstarDQuadForm`
is separately ALREADY known `U`-dependent, `CovariantHj.dstarDQuadForm_genuinely_U_dependent`, on a
DIFFERENT witness config — the two are not claimed to cancel, and no claim is made that they do). -/
theorem deltaQuadForm_deltaPrime_component_genuinely_U_dependent :
    deltaQuadForm (trivialU (L := AdmissibleSubspace.witnessL)) deltaWitnessConfig ≠
      deltaQuadForm witnessU deltaWitnessConfig ∨
    dstarDQuadForm (trivialU (L := AdmissibleSubspace.witnessL)) deltaWitnessConfig ≠
      dstarDQuadForm witnessU deltaWitnessConfig := by
  by_cases hD : dstarDQuadForm (trivialU (L := AdmissibleSubspace.witnessL)) deltaWitnessConfig =
      dstarDQuadForm witnessU deltaWitnessConfig
  · left
    intro hcon
    apply deltaPrimeQuadForm_genuinely_U_dependent
    unfold deltaQuadForm at hcon
    rw [hD] at hcon
    exact add_left_cancel hcon
  · right; exact hD

#print axioms deltaQuadForm_deltaPrime_component_genuinely_U_dependent

/-! ## §11 — STAGE 7 CONVENTION PIN (coordinator directive, filed against the module docstring's
"Convention inherited" residual, after the sibling `hj_experiment`/`hjcov.py` measurement showed a
no-transport convention next to a genuinely covariant object is gauge-VARIANT at measurable scale
— 4.3e-5 at 0.001 rad/site rising to 30.1% at 1.0 rad on the `d3` witness. That measurement makes
the "untransported vs `φ`-transported" choice a PINNED, discriminable fact about THIS file, not a
docstring caveat.

`φ : X ↦ iX` (`SuTwoInner.lean`'s own map, anti-Hermitian `↦` Hermitian) is not `SuTwo`-valued
(`i·(anti-Hermitian)` is Hermitian, leaving the submodule), so the TRANSPORTED reading is built at
the `Matrix (Fin 2) (Fin 2) ℂ` level directly: scale the coerced curl/commutator by `Complex.I`
BEFORE squaring/bracketing, exactly mirroring what substituting Bałaban's own `paper_A = i·A` into
his literal formula would compute. -/

/-- **The `φ`-TRANSPORTED first term**: `X` replaced by `φ(X) = i·X` (matrix-level, since `φ(X)`
leaves `SuTwo`) before squaring. -/
noncomputable def deltaPrimeFirstTermTransported
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  (Matrix.trace
      ((Complex.I • (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ)) *
          (Complex.I • (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ)) *
        (reHolonomy U p - 1))).re

/-- **The `φ`-TRANSPORTED commutator sum**: each `A′_i` replaced by `φ(A′_i) = i·A′_i`
(matrix-level) before bracketing; the formula's OWN leading `Complex.I` factor (present in
Bałaban's (3.10) itself, not part of the transport) is unchanged. -/
noncomputable def commutatorMatrixSumTransported
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : Matrix (Fin 2) (Fin 2) ℂ :=
  let a1 : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ)
  let a2 : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ)
  let a3 : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ)
  let a4 : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ)
  Complex.I •
    ((a1 * a2 - a2 * a1) + (a1 * a3 - a3 * a1) + (a1 * a4 - a4 * a1) +
      (a2 * a3 - a3 * a2) + (a2 * a4 - a4 * a2) + (a3 * a4 - a4 * a3))

/-- **The `φ`-TRANSPORTED second term.** -/
noncomputable def deltaPrimeSecondTermTransported
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  (Matrix.trace (commutatorMatrixSumTransported U A p * imHolonomy U p)).re

/-- **`commutatorMatrixSumTransported = -commutatorMatrixSum`** — each of the 6 brackets picks up
`i²=-1` from its two transported factors, and the leading `Complex.I` factor is common to both, so
it factors out. -/
theorem commutatorMatrixSumTransported_eq_neg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    commutatorMatrixSumTransported U A p = -commutatorMatrixSum U A p := by
  unfold commutatorMatrixSumTransported commutatorMatrixSum
  simp only [smul_mul_smul_comm, Complex.I_mul_I]
  module

/-- **`deltaPrimeFirstTermTransported = -deltaPrimeFirstTerm`** — `φ(X)² = i²X² = -X²`. -/
theorem deltaPrimeFirstTermTransported_eq_neg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    deltaPrimeFirstTermTransported U A p = -deltaPrimeFirstTerm U A p := by
  unfold deltaPrimeFirstTermTransported deltaPrimeFirstTerm
  rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, neg_mul, Matrix.trace_neg,
    Complex.neg_re]

/-- **`deltaPrimeSecondTermTransported = -deltaPrimeSecondTerm`.** -/
theorem deltaPrimeSecondTermTransported_eq_neg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    deltaPrimeSecondTermTransported U A p = -deltaPrimeSecondTerm U A p := by
  unfold deltaPrimeSecondTermTransported deltaPrimeSecondTerm
  rw [commutatorMatrixSumTransported_eq_neg, neg_mul, Matrix.trace_neg, Complex.neg_re]

#print axioms commutatorMatrixSumTransported_eq_neg
#print axioms deltaPrimeFirstTermTransported_eq_neg
#print axioms deltaPrimeSecondTermTransported_eq_neg

/-- **NAMING THE GAUGE ACTION** (coordinator correction to the Stage 7 dispatch, filed IN-FILE,
not left to prose alone). `curlValueCovariant`, hence `deltaPrimeFirstTerm`'s `X` and every
`AprimeXY`/`AprimeYZ`/`AprimeZW`/`AprimeWX` component built from it, is constructed from `RMap`,
the NONABELIAN adjoint action `R(U)X = UXU⁻¹` (`RMap_coe_apply`, `CovariantOperators.lean`) —
this is `hsInner`'s OWN proved invariance group (cited below, not reasserted), and it is a
DIFFERENT gauge law from CMP95 §1's `Q_k` sector (eq. 1.18: a bare weighted sum, no `Ad(g)`,
covariant instead under eq. 1.20's ABELIAN gradient shift `A ↦ A - ∂^η λ`, under which flat
summation is trivially covariant by linearity, and under which CMP95's OWN `Δ_k` (eq. 1.19) is
correctly `U`-INDEPENDENT — the flat sector this campaign already refuted as a candidate for THIS
covariant carrier, `DELTA_J_PINNING.md`). `deltaPrimeQuadForm`'s untransported convention, and the
`deltaPrimeQuadFormTransported_eq_neg` sign-flip below, are BOTH stated relative to this SAME
`Ad`-conjugation action — a convention pin is meaningless without naming the action it is pinned
relative to, and this is that name, anchored in a fact already proved (not asserted fresh here). -/
theorem hsInner_invariant_under_the_relevant_gauge_action
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    hsInner (RMap U X) (RMap U Y) = hsInner X Y :=
  hsInner_RMap U X Y

#print axioms hsInner_invariant_under_the_relevant_gauge_action

/-- **THE `φ`-TRANSPORTED `Δ′` quadratic form.** -/
noncomputable def deltaPrimeQuadFormTransported
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, (deltaPrimeFirstTermTransported U A p +
    deltaPrimeSecondTermTransported U A p)

/-- **THE PIN, fully general**: `deltaPrimeQuadFormTransported = -deltaPrimeQuadForm`, for ANY
`U, A, L`. This is the ALGEBRAIC content of the residual — the two conventions are not merely
"possibly different", they are a global SIGN FLIP of each other, everywhere. -/
theorem deltaPrimeQuadFormTransported_eq_neg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeQuadFormTransported U A = -deltaPrimeQuadForm U A := by
  unfold deltaPrimeQuadFormTransported deltaPrimeQuadForm
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTermTransported_eq_neg, deltaPrimeSecondTermTransported_eq_neg]
  ring

#print axioms deltaPrimeQuadFormTransported_eq_neg

/-- **THE CONTROL**: at the trivial background, the two conventions COINCIDE (both `0`) — this is
EXACTLY why a trivial/near-trivial witness cannot discriminate them (the coordinator's own
diagnosis of the sibling `hjcov.py` measurement: the gauge-variance signature vanishes as the
background approaches the identity). A check run ONLY at `trivialU` would pass under EITHER
convention and prove nothing about which one is intended. -/
theorem deltaPrimeQuadFormTransported_vanishes_at_trivial (A : Bond L → SuTwo) :
    deltaPrimeQuadFormTransported (trivialU (L := L)) A = 0 := by
  rw [deltaPrimeQuadFormTransported_eq_neg, deltaPrimeQuadForm_vanishes_at_trivial]
  ring

#print axioms deltaPrimeQuadFormTransported_vanishes_at_trivial

/-- **THE DISCRIMINATOR — the pin's headline result, relative to the NAMED action**
(`hsInner_invariant_under_the_relevant_gauge_action` above: the nonabelian `Ad`-conjugation
`R(U)X=UXU⁻¹`, NOT CMP95 §1's abelian gradient shift). At `witnessU`, a background GENUINELY far
from the identity (`witnessM = !![0,1;-1,0]`, a `90°` rotation under exactly THIS `Ad` action — no
small-angle/near-trivial assumption anywhere in its construction), the two conventions give
DIFFERENT, both nonzero, values: `8` (untransported, this file's committed convention, matching
`curlValueCovariant`/`dstarDQuadForm`, both built from the SAME `RMap` action) vs `-8`
(`φ`-transported). The SAME witness gives `0 = 0` at `trivialU` (previous theorem) — so this
witness is a genuine discriminator (fails to distinguish at the control point, succeeds away from
it under the named action), not a check that passes vacuously everywhere. -/
theorem deltaPrimeQuadForm_conventions_differ_at_witnessU :
    deltaPrimeQuadFormTransported witnessU deltaWitnessConfig ≠
      deltaPrimeQuadForm witnessU deltaWitnessConfig := by
  rw [deltaPrimeQuadFormTransported_eq_neg, deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq]
  norm_num

theorem deltaPrimeQuadFormTransported_witnessU_eq :
    deltaPrimeQuadFormTransported witnessU deltaWitnessConfig = -8 := by
  rw [deltaPrimeQuadFormTransported_eq_neg, deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq]

#print axioms deltaPrimeQuadForm_conventions_differ_at_witnessU
#print axioms deltaPrimeQuadFormTransported_witnessU_eq

/-! **VERDICT, stated in-file (not left to prose alone)**: the untransported/transported choice is
a GLOBAL SIGN FLIP (`deltaPrimeQuadFormTransported_eq_neg`, fully general, no witness needed to
state — only to DISTINGUISH the two, since they agree identically at any `U`-configuration for
which `Δ′` itself is `0`, e.g. the trivial background). This file's `deltaPrimeQuadForm` (and
hence `deltaQuadForm`) is committed to the UNTRANSPORTED reading, for internal consistency with
`curlValueCovariant`/`dstarDQuadForm` (LAW-19: a per-file divergent convention would break
`Δ = D*D + Δ′`'s own internal coherence more than it would fix any one term in isolation). Which
convention is Bałaban's OWN intended reading is NOT settled by this file — that determination
needs the SAME question resolved for `curlValueCovariant` itself (whether CMP99b's `D_U^ηA`
formula, eq. (3.3)/(3.4), is stated for his Hermitian `A` directly or for an anti-Hermitian
generator), which is exactly the sibling question posed to the `CovariantHjMinimizer` lane against
CMP95 eq. 1.18/1.20's `Q_k`. If that lane's render settles `curlValueCovariant`'s own convention as
Hermitian-`A`-literal (transported), THIS file's convention flips too
(`deltaPrimeQuadFormTransported` becomes the correct reading) — a coordinated, cross-file decision,
not a unilateral one, exactly as the coordinator directed. -/

/-! ## §12 — THE FAITHFUL ASSEMBLY (added 2026-07-22 after the K3 gate's finding F3)

`deltaQuadForm` above is the WRONG-SIGN assembly under this tree's anti-Hermitian carrier (see its
docstring). This section supplies the faithful one so consumers have a correct object to reach for
rather than a warning to remember. -/

/-- **CMP99b eq. (3.10), FAITHFULLY assembled for this tree's anti-Hermitian `SuTwo` carrier.**
`dstarDQuadForm` already carries the `φ`-transport through `hsInner`; `Δ′`'s raw-trace terms do not,
so the TRANSPORTED reading is the faithful one. Equivalently `D*D − Δ′` in this file's untransported
convention. Confirmed by an independent third-family (Kimi K3) cold re-derivation from its own
renders of CMP99b pp.390-392. -/
noncomputable def deltaQuadFormFaithful
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  dstarDQuadForm U A + deltaPrimeQuadFormTransported U A

/-- The faithful assembly equals `D*D − Δ′` in the untransported convention. Immediate from the
already-proved general pin `deltaPrimeQuadFormTransported_eq_neg`. -/
theorem deltaQuadFormFaithful_eq_sub
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaQuadFormFaithful U A = dstarDQuadForm U A - deltaPrimeQuadForm U A := by
  unfold deltaQuadFormFaithful
  rw [deltaPrimeQuadFormTransported_eq_neg]
  ring

/-- **The two assemblies GENUINELY DIFFER** — the discrepancy is not notional. At the non-central
`witnessU` background they differ by twice the `Δ′` value, so a consumer that reaches for the wrong
one gets a different number. -/
theorem deltaQuadForm_ne_faithful_of_deltaPrime_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (h : deltaPrimeQuadForm U A ≠ 0) :
    deltaQuadForm U A ≠ deltaQuadFormFaithful U A := by
  rw [deltaQuadFormFaithful_eq_sub]
  unfold deltaQuadForm
  intro hEq
  apply h
  linarith [hEq]


end AdalyFormal.Balaban.DeltaPrime
