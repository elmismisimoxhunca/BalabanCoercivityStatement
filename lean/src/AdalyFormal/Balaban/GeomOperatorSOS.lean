import AdalyFormal.Balaban.GeomGlobal

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! # `(geom)` via the DIRECT operator-SOS LATTICE identity (route R2) — the REAL engine.

This module is the route-R2 counterpart of `BlochPSD.lean`.  Where `BlochPSD` proves the residual
`(geom)` by the block-Fourier symbol `M̂(k) ⪰ 0 ∀k` (a complex-Hermitian trig-matrix positivity,
whose SOS certificate `hSOS` is a `3757`-entry Gram identity — now kernel-checkable via the
`RatSOSEval` integer-scaled balanced-tree reflection, ~37s `rfl`, axiom-clean; the earlier
"will not kernel-check at scale" was an encoding artifact, refuted 2026-07-25),
this module records the strictly-real LATTICE operator sum-of-squares that BYPASSES the Fourier
transform entirely:

    `geomForm ell B  =  ∑ᵢ dᵢ · ‖Sᵢ B‖²`   for `B ∈ admissibleSubspaceInter L ell`,

where `geomForm ell B := LHS(geom) − RHS(geom)` (so `GeomInequality ell B ↔ 0 ≤ geomForm ell B`),
each `Sᵢ` is a BAND-1 translation-invariant block operator on the 17-component free-cell field
(`z_μ ↔ block-shift e_μ`), and `dᵢ ≥ 0` rational.  Because every summand is `dᵢ ≥ 0` times a real
square, positivity is IMMEDIATE (`sosForm_nonneg`) — no torus quantifier, no complex arithmetic, no
Fejér–Riesz.  The whole content is the finite algebraic IDENTITY `geomForm = ∑ᵢ dᵢ‖Sᵢ B‖²`.

## What is PROVED here (no `sorry`).

* `sosForm_nonneg` — the real operator-SOS engine: `0 ≤ ∑ᵢ dᵢ · ∑_R (valᵢ R)²` whenever `dᵢ ≥ 0`.
  Reusable for ANY lattice quadratic form written as a coefficient-nonnegative sum of squares.
* `geomForm`, `geomInequality_iff_geomForm_nonneg` — the exact rearrangement
  `GeomInequality ell B ↔ 0 ≤ geomForm ell B`.
* `geomInequality_of_sosIdentity` — **the R2 reduction**: ANY witness `(d ≥ 0, val)` together with the
  identity `geomForm ell B = ∑ᵢ dᵢ ∑_R (valᵢ R)²` proves `GeomInequality ell B`.  This is the engine
  that consumes the certificate; it is the real-space analogue of `blochPSD_of_gramReproduction`.

## The certificate (exact, in `compute/geom_op_sos/`).

`lattice_sos.py` (SELFHASH `c02bc47d23da330ca553281e1b6003d1c84c2eea46eb7e0ee5e9f1ab84764efa`,
`PYTHONHASHSEED=0`, dual-run byte-identical): the `(dᵢ, Sᵢ)` are the exact rational SOS
`compute/blochpsd/cert_data.json` — `1243` squares, `dᵢ ≥ 0`, `3428` covector terms, band-1
monomials `{1,z₀,z₁,z₂}`, free-cell dim `17`.  Translating `z_μ ↔ e_μ`, the real-space quadratic
form `∑_R ∑ᵢ dᵢ (Sᵢ B)(R)²` was verified to reproduce the `(geom)` form matrix `M_free` (built from
the Lean-faithful energy definitions `coarseQEnergy`, `slabCurlEnergy`, `inBlockBondEnergy`,
`bondNormSq` via `blochpsd/exact_symbol.py`) restricted to `admissibleSubspaceInter`
**ENTRY-BY-ENTRY, residual EXACTLY 0**, on real periodic lattices at `m=3` (N=6) and `m=4` (N=8)
blocks/axis — SIZE-UNIFORM.  The free-mask was verified translation-invariant (the 17-index free cell
tiles every block).  `controls.py` (SELFHASH
`aa56f64a84ac476b5a8d4bafc07e169afa9bc1b3b1465c3c6a0330fb2aeec7f0`): `5/5` independent mutations
(double a `dᵢ`, perturb a covector entry, wrong band-1 shift, drop a square, S82 garbage `dᵢ≡1`)
each drive the residual nonzero — the identity check is NON-VACUOUS.

## The single named residual to a KERNEL closure of `(geom)`.

`geomInequality_of_sosIdentity` consumes the identity `geomForm ell B = ∑ᵢ dᵢ ∑_R (valᵢ R)²`.  The
ONE thing not kernel-proved is that identity for the census certificate.  Its size-uniform structure
(established numerically above, and matching `GeomScratch`'s per-block reindexing of the four
energies — `sum_topFace_eq_Sbet` already gives `bondNormSq − inBlockBondEnergy = ∑_c topFaceEnergy`)
is: `geomForm = ∑_R LocalGeom_R` with each `LocalGeom_R` a FIXED band-1 quadratic form, and the
per-block identity `LocalGeom_R(B) = ∑ᵢ dᵢ (Sᵢ B)(R)²` (on `admissibleSubspaceInter`, where the
non-free bonds vanish) is one FIXED rational polynomial identity in the `≤ 68` free-bond values of
the band-1 neighbourhood — provable ONCE, independent of lattice size, then summed by
`Finset.sum_congr`.  What a Lean closure still needs: (i) the per-block reindexing of `coarseQEnergy`
and `slabCurlEnergy` into free coordinates (the `bondNormSq`/`inBlockBondEnergy` halves already exist
in `GeomScratch`); (ii) the fixed `68`-variable rational identity `LocalGeom_0 = ∑ᵢ dᵢ (Sᵢ)²` (the
census certificate, `ring`/`norm_num` over ℚ); (iii) its translation-covariant transport to every
block `R` (`CoarseShiftCovariance`).  NOTHING here is asserted PROVED that is not; no `sorry` in this
module.  `GeomGlobal.geomInequality_of_admissible_ell2` remains the honest open `sorry` (scoped to
`ell = 2`, the only case the certificate covers); step (ii), the fixed ℚ-identity, was MEASURED not to
kernel-check by reflection (`compute/geom_cert/FINDINGS.md`, residual `[RES-CERT-KERNEL-REFLECT]`). -/

namespace GeomOperatorSOS

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.Lemma24Assembly
open GeomGlobal

variable {L : PeriodicLatticeExtent}

/-- **The real operator-SOS engine (PROVED, no `sorry`).** A coefficient-nonnegative finite sum of
real squares is nonnegative: `0 ≤ ∑ᵢ dᵢ · ∑_R (valᵢ R)²` when every `dᵢ ≥ 0`.  Here `valᵢ R` is the
real value `(Sᵢ B)(R)` of the `i`-th band-1 block operator at block `R`; the double sum is exactly
`∑ᵢ dᵢ ‖Sᵢ B‖²`.  This is the route-R2 positivity core — no complex arithmetic, no torus. -/
theorem sosForm_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (val : ι → κ → ℝ) :
    0 ≤ ∑ i, d i * ∑ R, (val i R) ^ 2 := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hd i) (Finset.sum_nonneg fun R _ => sq_nonneg _)

/-- `geomForm ell B := LHS(geom) − RHS(geom)`.  By construction `GeomInequality ell B` (which is
`LHS ≥ RHS`) is exactly `0 ≤ geomForm ell B` (`geomInequality_iff_geomForm_nonneg`). -/
noncomputable def geomForm (ell : ℕ) (B : Bond L → ℝ) : ℝ :=
  (ell : ℝ) * coarseQEnergy ell B + (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B
    - ((1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
        - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B)

/-- **`GeomInequality ell B ↔ 0 ≤ geomForm ell B`** (PROVED).  Pure rearrangement. -/
theorem geomInequality_iff_geomForm_nonneg (ell : ℕ) (B : Bond L → ℝ) :
    GeomInequality ell B ↔ 0 ≤ geomForm ell B := by
  unfold GeomInequality geomForm
  constructor <;> intro h <;> linarith

/-- **THE R2 REDUCTION (PROVED, no `sorry`).** Any operator-SOS witness for `geomForm` — nonnegative
coefficients `d` and block-operator values `val` with the identity
`geomForm ell B = ∑ᵢ dᵢ · ∑_R (valᵢ R)²` — proves `GeomInequality ell B`.  This is what the exact
rational certificate `compute/geom_op_sos/` discharges (residual 0, size-uniform); the only unbanked
step is that identity in the kernel (see the module docstring).  Real-space analogue of
`BlochPSD.blochPSD_of_gramReproduction`, but with the positivity trivial (no torus, no ℂ). -/
theorem geomInequality_of_sosIdentity {ι κ : Type*} [Fintype ι] [Fintype κ]
    {ell : ℕ} (B : Bond L → ℝ)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (val : ι → κ → ℝ)
    (hIdent : geomForm ell B = ∑ i, d i * ∑ R, (val i R) ^ 2) :
    GeomInequality ell B := by
  rw [geomInequality_iff_geomForm_nonneg, hIdent]
  exact sosForm_nonneg d hd val

/-- **The named residual, as an explicit proposition.** `(geom)` for admissible `B` is discharged by
route R2 exactly when this holds: there is a finite operator-SOS witness whose identity reproduces
`geomForm`.  Verified over ℚ, entry-by-entry, residual 0, size-uniform in `compute/geom_op_sos/`
(the census certificate `compute/blochpsd/cert_data.json`, `1243` squares).  Stated here as the
precise target for a future kernel closure — NOT proved.  (Whoever closes it feeds the witness to
`geomInequality_of_sosIdentity`; positivity is then free.) -/
def HasOperatorSOS (ell : ℕ) (B : Bond L → ℝ) : Prop :=
  ∃ (m N : ℕ) (d : Fin m → ℝ) (val : Fin m → Fin N → ℝ),
    (∀ i, 0 ≤ d i) ∧ geomForm ell B = ∑ i, d i * ∑ R, (val i R) ^ 2

/-- If the operator-SOS witness exists for admissible `B`, `(geom)` holds — immediate from the R2
reduction.  (PROVED: it just unpacks `HasOperatorSOS` into `geomInequality_of_sosIdentity`.) -/
theorem geomInequality_of_hasOperatorSOS {ell : ℕ} (B : Bond L → ℝ)
    (h : HasOperatorSOS ell B) : GeomInequality ell B := by
  obtain ⟨m, N, d, val, hd, hIdent⟩ := h
  exact geomInequality_of_sosIdentity B d hd val hIdent

#print axioms sosForm_nonneg
#print axioms geomInequality_iff_geomForm_nonneg
#print axioms geomInequality_of_sosIdentity
#print axioms geomInequality_of_hasOperatorSOS

end GeomOperatorSOS
