import AdalyFormal.Balaban.GeomScratch
import AdalyFormal.Balaban.RatSOSEval

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! # `(geom)` — the GLOBAL (joint cross-sectional) reduction, and the UNIFORMITY verdict.

This module records the resolution of the crux question left open by `GeomScratch.lean`: whether the
U=1 (CMP96 Lemma 2.4 / (2.128)) operator positivity, reduced to the single residual `(geom)`

    ell·Q + ell⁻²·slabCurl  ≥  (1/3)ell⁻³·(‖B‖²−Sin) − 6ell⁻²·Sin   on `admissibleSubspaceInter`,

is UNIFORM in the lattice size or DEGRADES (the k-uniformity coercivity crux surfacing at U=1).

## VERDICT — UNIFORM (the crux does NOT surface at U=1).

Numeric certificate `compute/geom_global/` (`PYTHONHASHSEED=0`, dual-run byte-identical):

* `ladder.py`  (hash f975ea77c10eeae7585c0189b48d20431a265e7009eaa336ea8544f1648d24b8):
  the admissible-subspace margin (min eigenvalue of the `(geom)` quadratic form restricted to
  `admissibleSubspaceInter`, faithful to the Lean `staircasePath` (2,1,0) gauge) is
  **EXACTLY +0.07727733** for the whole isotropic ladder N=4,6,8,10,12 AND the elongated ladder
  N=(4,4,K), K∈{4,6,8,10,12,16,20,24}, at ell=2.  The margin does NOT shrink as the lattice grows —
  it is identical.  `ladder_ell3.py` (hash ab0d06fec2bba12436b2c3758427bb26f155a0aa07f1cc2f92f8de6a80ff7abc)
  confirms the SAME uniformity at **ell=3**: margin **EXACTLY +0.02158515** across ISO N=6,9,12 and
  ELONG N=(6,6,K), K∈{6,9,12,15,18} (spread 1.3e-14).  So the verdict holds at both ell∈{2,3}.

* `structure.py`  (hash 08d0fb57c09a1a47f6699762aefc5968be337e1abf078c9739cdc34edd454146):
  the softest eigenvalue is **non-degenerate (multiplicity 1)**, the form is **finite-range**
  (L∞ block-step ≤ 1: coupling zero beyond neighbouring blocks), and mutation controls C1/C2/C3
  confirm the constancy is real (perturbing the form / dropping admissibility / rescaling the
  ell-coefficients all MOVE the margin).

* `bloch.py`  (hash bf706ff630299c263cd0a5169c76304a7652e6db77ed6f1098755bd2ba61a7a4)
  and `census.py`  (hash 3a2e3838b7e9cbacf70582abea1a605b015a8fc3cab0df15640f823c01bc33b8):
  the form is block-translation-invariant, so under the block-Fourier transform it decomposes into a
  fixed 17×17 Hermitian matrix **Bloch symbol** `M̂(k)` on the free cell bonds (24 cell bonds, 7
  fixed by the translation-invariant staircase gauge), with a **13-block L∞ stencil** (self + 6 axis
  + 6 edge-diagonal neighbours, the edge-diagonals coming from the shared curl plaquettes — the JOINT
  coupling).  Over the momentum torus, `λ_min(M̂(k))` attains its **minimum +0.07727733 at k=0**
  (the block-PERIODIC mode).  This RIGOROUSLY EXPLAINS the exact size-independence: for every lattice
  the min-eig equals `λ_min(M̂(0))`, a fixed matrix independent of size.

## WHY uniform, and the shape of the global proof.

`(geom)`'s form is a FINITE-RANGE, block-translation-invariant quadratic form (`coarseQEnergy`
within a block, `slabCurl` on the neighbouring-block stencil, the `Sin`/`Sbet` split diagonal), and
`admissibleSubspaceInter` is block-translation-invariant (the `staircasePath` gauge fixes the same
per-block pattern).  Hence its admissible spectrum is the union over Bloch momenta of the finite
symbol spectra, and the minimum is attained at the block-periodic momentum k=0, which is present on
every lattice with ≥ 2 blocks per axis.  So `(geom)` on ANY admissible lattice is EQUIVALENT to

    (BlochPSD)   `M̂(k) ⪰ 0` for all k ∈ T³,   with min +0.07727733 attained at k=0.

The naive further reduction "prove `M̂(0) ⪰ 0` alone" is FALSE: `bloch.py` step (3) shows
`M̂(k) − M̂(0)` is INDEFINITE (min −3.4 near k≈(π,π,π)), so the ordering `M̂(k) ⪰ M̂(0)` does not
hold; the residual is genuinely the FULL symbol positivity `(BlochPSD)`.  This is the JOINT
cross-sectional operator the task predicted, and it is exactly why the per-coarse-BOND SOS is dead:
`compute/geom_assembly/perc_certificate.py` proved the per-`c` remainder `diag(R)` indefinite
(R=−1 on transverse ν-edge / cross-block bonds); those ν-edge terms are precisely the edge-diagonal
(offset-(1,1,0)-type) block couplings the census exhibits — they require the joint 13-block stencil,
not a per-bond diagonal correction.

## STATUS in this module — ⚠ SUPERSEDED 2026-07-28: THIS MODULE IS NOW `sorry`-FREE.

**Correction (2026-07-28, S75 in-place, old text retained struck).**  The two `sorry`-carrying stubs
that used to sit at the end of this file (`geomInequality_of_admissible_ell2` and
`lemma24_unconditional_U1_ell2`) HAVE BEEN DELETED.  They were never open mathematics: both results
were already proved in `AdalyFormal.Balaban.HrefReduction`, and the `sorry`s existed ONLY because
`HrefReduction` sits DOWNSTREAM of this module, so this module could not import the closed proofs.
Both names now live — with byte-identical signatures and NO `sorry` — in the leaf module
`AdalyFormal.Balaban.GeomBaseClosed`, which imports both sides.  `GeomGlobal.<same name>` therefore
still resolves; import `GeomBaseClosed` to get it.  Measured axiom cones, before → after:
`GeomGlobal.geomInequality_of_admissible_ell2`
  `{propext, sorryAx, Classical.choice, Quot.sound}` → `{propext, Classical.choice, Quot.sound}`;
`GeomGlobal.lemma24_unconditional_U1_ell2` likewise.  The statement identity was checked
mechanically against the stub before deletion (`compute/geom_cycle/CONTROLS.log`: an `Eq` between the
stub and `HrefReduction.geomInequality_of_admissible_ell2_uncond` elaborates, i.e. the two `Prop`s are
definitionally equal, with two must-fail controls firing).

~~`geomInequality_of_admissible_ell2` below is the SINGLE remaining open residual at `ell = 2`,
`(geom)` equivalently `(BlochPSD)` — registered honestly as a `sorry` (a residual IS a sorry).  Its
dependents transparently inherit `sorryAx` (see `#print axioms`).~~  `lemma24_unconditional_of_geom` is
the kernel-clean reduction (= `GeomScratch.lemma24_from_geom` re-exposed, PROVED, no `sorry`): it turns
any proof of `(geom)` into `Lemma24Conclusion` unconditionally at any `ell ≥ 2`.  ~~Chaining it at
`ell = 2` gives `lemma24_unconditional_U1_ell2`, `sorry`-backed VIA the named residual only.~~
Chaining it at `ell = 2` is done in `GeomBaseClosed`, unconditionally.

**HONEST SCOPE.**  ⚠ The two `[RES-…]` residuals named in this paragraph are BOTH CLOSED as of
2026-07-26 (`HrefQSlab.hQS_proved`, `HrefRefl.hrefl_proved`), so the "one open step" sentence below is
SUPERSEDED — retained struck for the record.  The `ell = 2` SCOPE statement is unchanged and still
binding: `ell = 3` is a different 55-index symbol and is NOT built (`[RES-CERT-ELL3]`).

~~The residual and the milestone lemma are `ell = 2` SPECIFICALLY, not `∀ ell ≥ 2`:
the only backing object is the `ell = 2`, 17-index operator-SOS certificate
`compute/blochpsd/cert_data.json`; `ell = 3` is a different 55-index symbol, not built
(`[RES-CERT-ELL3]`).  A grade-3 gate convicted the previous `∀ ell` form as an over-claim.  The one
open step is the `ell = 2` `(geom)` = 13-block-stencil Bloch-symbol positivity, numerically true with
margin +0.0773 at k=0; its Lean closure is blocked by two named residuals `[RES-GEOM-REINDEX]` (the
whole-lattice → free-cell reindexing, unbuilt) and `[RES-CERT-KERNEL-REFLECT]` (the fixed Gram
ℚ-identity).  **`[RES-CERT-KERNEL-REFLECT]` is now MEASURED FEASIBLE** (2026-07-25,
`compute/rat_sos_eval/FEASIBILITY.md`), correcting the earlier "does not kernel-check" verdict which
was an ENCODING artifact (Mathlib `List.filter/map/sum`-in-`decide` over a super-linear left-nested
fold).  The integer-scaled Gram identity (1243 squares, 26808 leaf multiply-adds, `W = 921600`)
kernel-checks by `rfl` in ~38 s with `#print axioms` clean and NO `native_decide`, using
balanced-tree association; a corrupted-leaf mutation makes the `rfl` fail (non-vacuous).  The reusable
evaluator `AdalyFormal.Balaban.RatSOSEval` now exists (proved, axiom-clean); what remains for a full
kernel discharge is the covector-faithful sparse-Gram wiring feeding `RatSOSEval.gram sqsI = T` to
`RatSOSEval.quadForm_nonneg_of_intGram`, plus `[RES-GEOM-REINDEX]`.~~ -/

namespace GeomGlobal

open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.Lemma24Assembly
open AdalyFormal.Target.ClayStatement

variable {L : PeriodicLatticeExtent}

/-- The `(geom)` inequality as a named proposition — the summed per-coarse-bond cross-sectional
operator positivity, LHS `ell·Q + ell⁻²·slabCurl`, RHS `(1/3)ell⁻³·Sbet − 6ell⁻²·Sin`. -/
def GeomInequality (ell : ℕ) (B : Bond L → ℝ) : Prop :=
  (ell : ℝ) * coarseQEnergy ell B + (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B
      ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
        - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B

/-- **Consumer of `RatSOSEval` (PROVED, no `sorry`).** Given the `ell = 2` free-cell integer
operator-SOS certificate — nonnegative integer coefficients `hpos` together with the (strict-kernel,
`native_decide`-free, MEASURED-feasible in ~38 s) integer Gram identity `hgram : ∀ a b,
RatSOSEval.gram sqsI a b = T a b` — the free-cell quadratic form of the integer target `T` is
nonnegative for every real assignment `x`.  This is exactly the engine that discharges the
SOS-identity half of `(geom)` (`geomForm 2 B = LocalGeom₀`, `LocalGeom₀ = Σᵢ dᵢ(Sᵢ)²`): once
`[RES-GEOM-REINDEX]` supplies the free-cell coordinates `x = freecoord B` and the identification
`geomForm 2 B = Σ_{a,b} (T a b) xₐx_b`, this lemma delivers `0 ≤ geomForm 2 B`, i.e.
`GeomInequality 2 B`.  Proof is a direct application of `RatSOSEval.quadForm_nonneg_of_intGram`. -/
theorem freecell_quadForm_nonneg {V : ℕ}
    (sqsI : List (ℤ × (Fin V → ℤ))) (hpos : ∀ s ∈ sqsI, 0 ≤ s.1)
    (T : Fin V → Fin V → ℤ) (hgram : ∀ a b, RatSOSEval.gram sqsI a b = T a b)
    (x : Fin V → ℝ) :
    0 ≤ ∑ a, ∑ b, ((T a b : ℤ) : ℝ) * (x a * x b) :=
  RatSOSEval.quadForm_nonneg_of_intGram sqsI hpos T hgram x

/-- **The kernel-clean reduction (PROVED, no `sorry`).** Any proof of `(geom)` yields
`Lemma24Conclusion` unconditionally at `ell ≥ 2` (in particular `ell ∈ {2,3}`).  This is
`GeomScratch.lemma24_from_geom` exposed against the named `GeomInequality`. -/
theorem lemma24_unconditional_of_geom {ell : ℕ}
    (hell2 : 2 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (hGeom : GeomInequality ell B) :
    Lemma24Conclusion ell B :=
  lemma24_from_geom hell2 hstrict0 hstrict1 hstrict2 hdvd B hB hGeom

/-! **HISTORICAL RECORD — 2026-07-28: THE `(geom)` RESIDUAL DESCRIBED BELOW IS CLOSED.**  It is
proved `sorry`-free by `AdalyFormal.Balaban.HrefReduction.geomInequality_of_admissible_ell2_uncond`
and re-exported under its original name by `AdalyFormal.Balaban.GeomBaseClosed`.  Both blockers named
below — `[RES-GEOM-REINDEX]` and `[RES-CERT-KERNEL-REFLECT]` — are discharged
(`HrefQSlab.hQS_proved`, `HrefRefl.hrefl_proved`).  The text is kept as the evidence trail; per S75
every sentence below that asserts something is OPEN is struck in place.  The `ell = 2` SCOPE claims are
NOT struck: they are still binding (`ell = 3` is a different 55-index symbol, `[RES-CERT-ELL3]`).

~~THE SINGLE OPEN RESIDUAL, HONESTLY SCOPED TO `ell = 2` — `(geom)` for the concrete SOS
certificate.  Numerically TRUE~~
certificate.**  Numerically TRUE with a uniform, size-independent margin +0.07727733 (min attained at
the block-periodic Bloch momentum k=0), reduced to the fixed 13-block-stencil Hermitian Bloch-symbol
positivity `M̂(k) ⪰ 0 ∀k` — see the module docstring and `compute/geom_global/`.  Registered as a
`sorry` (a residual IS a sorry); NOT proved here.

**WHY `ell = 2` and not `∀ ell ≥ 2` (over-quantification fix, 2026-07-25).**  The earlier form of this
lemma quantified `∀ ell ≥ 2`, but the ONLY object backing it — the exact rational operator-SOS
certificate `compute/blochpsd/cert_data.json` (1243 squares) — is the `ell = 2`, 17-index free-cell
symbol SPECIFICALLY.  `ell = 3` is a genuinely different 55-index symbol that is NOT built (named
residual `[RES-CERT-ELL3]`; Bałaban uses `L ∈ {2,3}`), and `ell ≥ 4` is unexamined.  A grade-3 gate
convicted the `∀ ell` statement as an over-claim: a `sorry` whose surrounding evidence (the docstring's
"reduced to the fixed certificate") covers only `ell = 2`.  So the statement now SAYS `ell = 2`.

**ROUTE R2 (real-space operator-SOS) — `GeomOperatorSOS.lean`.** For admissible `B` the `(geom)` form
has an equivalent strictly-real operator sum-of-squares `geomForm 2 B = Σᵢ dᵢ ‖Sᵢ B‖²`, `dᵢ ≥ 0`
rational, each `Sᵢ` a BAND-1 translation-invariant block operator on the 17-index free cell.  This
identity is verified EXACTLY over ℚ (residual 0, entry-by-entry) and SIZE-UNIFORM (m ∈ {3,4}) in
`compute/geom_op_sos/lattice_sos.py`; the census `symbol` was cross-checked to equal the independently
extracted geom stencil (`compute/geom_cert/collapse_check.py`, 7803 entries, residual 0 — so the SOS
genuinely reproduces the geom form, NOT itself).  `GeomOperatorSOS.geomInequality_of_hasOperatorSOS`
(PROVED, no `sorry`) turns any such witness into `GeomInequality 2 B` with positivity TRIVIAL (a real
sum of squares).  The residual is thereby SHARPENED to the single fixed finite ℚ-identity
`HasOperatorSOS 2 B`.

**WHY THIS `sorry` IS NOT DISCHARGED — two named residuals, one MEASURED.**
* `[RES-GEOM-REINDEX]` (the large one): a Lean closure needs the per-block reindexing of the whole-
  lattice energies `coarseQEnergy`/`slabCurlEnergy` into the 68 = 4×17 free-cell coordinates (only the
  `bondNormSq`/`inBlockBondEnergy` halves exist, `GeomScratch.sum_topFace_eq_Sbet`), plus its
  translation-covariant transport.  No free-cell coordinate framework exists in the tree yet; this is a
  multi-hundred-line combinatorial construction, deferred.
* `[RES-CERT-KERNEL-REFLECT]` (MEASURED FEASIBLE, 2026-07-25, `compute/rat_sos_eval/FEASIBILITY.md`):
  the fixed ℚ-identity `LocalGeom₀ = Σᵢ dᵢ (Sᵢ)²`, integer-scaled to `∀(a,b), Σᵢ wᵢ Lᵢ[a] Lᵢ[b] =
  W·M[a][b]` (`W = 921600`, 1243 squares, 26808 leaf multiply-adds), DOES kernel-check by `rfl` in
  ~38 s with `#print axioms` clean and NO `native_decide`.  The earlier "does not kernel-check"
  verdict (`compute/geom_cert/`) was an ENCODING artifact: it used Mathlib `List.filter/map/sum` inside
  `decide` over a LEFT-NESTED fold, which is super-linear in the kernel (`~K^1.6`; K=300 → 20 s).  The
  fix is (i) integer scaling — kernel `Int`/`Nat` arithmetic is GMP-accelerated, `Rat` normalization is
  not — and (ii) BALANCED-TREE association (linear kernel reduction, depth `O(log K)`, no deep spine).
  The custom reflected fast-arithmetic evaluator the old note said was "not one-lane work" now EXISTS
  and is proved axiom-clean: `AdalyFormal.Balaban.RatSOSEval` (`quadForm_nonneg_of_intGram`,
  `sosVal_eq_gramQuad`, `STree.eval_eq_leaves_sum`).  A corrupted-leaf mutation makes the check `rfl`
  fail (non-vacuous, OPS-3).  What remains for a full IN-LEAN discharge of this `sorry`: the covector-
  faithful sparse-Gram wiring (prove the emitted balanced-tree leaves ARE the covector products, with
  the completeness count) feeding `RatSOSEval.gram sqsI = T`; the arithmetic feasibility is settled.
  The per-coarse-BOND constant-multiplier SOS is separately PROVED impossible
  (`compute/geom_assembly/perc_certificate.py`), so the joint stencil is unavoidable.  This `sorry` is
  NOT discharged (it still needs the wiring above and `[RES-GEOM-REINDEX]`).

**ACCEPTED TORUS SCOPE — `hL : ∀ μ, 4 ≤ L μ` (owner ruling 2026-07-25).**  The backward-reindex route
(`Ell2Discharge`, `BackwardCert`) routes through `FreeCellFrame.freeCellBond`, which needs `4 ≤ L μ` on
every axis so the free-cell enumeration has ≥ 4 sites/direction and avoids wraparound collision, and it
needs `hstrict : 2 < L μ + 1` (`GeomScratch.sum_topFace_eq_Sbet`); `4 ≤ L μ ⟹ 2 < L μ + 1`, so `hL`
SUBSUMES `hstrict`.  `hL` excludes only the small degenerate lattices (`L μ ∈ {1}` one/three coarse
blocks per axis); the physical RG regime always satisfies it, so this is the faithful accepted torus
condition, NOT a weakening of the mathematical content.  With `hL` present the `Ell2Discharge`
adjudication's `L μ + 1 = 2` corner (which the backward telescoping cannot cover) is simply excluded by
hypothesis, and the residual is EXACTLY the reference-block SOS identity + transport
(`Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS`, axiom-clean reduction).~~ -/

/-! ## The two former `sorry` stubs are GONE (2026-07-28).

`geomInequality_of_admissible_ell2` and `lemma24_unconditional_U1_ell2` used to be declared here with
a `sorry` each, purely because the closed proofs live DOWNSTREAM (`HrefReduction`), which this module
cannot import (measured: the two simple import paths both end on `GeomOperatorSOS → GeomGlobal`).
They now live in the leaf `AdalyFormal.Balaban.GeomBaseClosed`, IN THIS SAME `GeomGlobal` NAMESPACE
and with byte-identical signatures, proved.  So `GeomGlobal.geomInequality_of_admissible_ell2` and
`GeomGlobal.lemma24_unconditional_U1_ell2` still resolve — add `import
AdalyFormal.Balaban.GeomBaseClosed`.  Statement identity against the deleted stubs was checked
mechanically BEFORE deletion, with two must-fail controls firing:
`compute/geom_cycle/CONTROLS.log`, `compute/geom_cycle/EVIDENCE_stub_type_eq_uncond.log`. -/

#print axioms lemma24_unconditional_of_geom

end GeomGlobal
