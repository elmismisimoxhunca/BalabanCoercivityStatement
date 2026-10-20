import AdalyFormal.Balaban.QSlabReflect

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! # `SparseGram` — the `ℓ=2` Q+Slab certificate as a COVECTOR-FAITHFUL sparse SOS, and its
GRAM-FREE positivity.

This module INSTANTIATES the reusable sparse soundness bridge of `RatSOSEval`
(`sosQuadValue`, `sosQuadValue_nonneg`, `scovEval_eq_denseSum`, `sosQuadValue_eq_sosVal`) on the
concrete 51-form Q+Slab certificate, discharging quadratic-form positivity **without** the dense
`80×80` Gram identity `∀ a b, gram qsSquares a b = T a b` that `QSlabReflect.qs_reflect_nonneg`
requires as a hypothesis and that was MEASURED not to `decide` in practical time (>7 min,
`compute/qslab_reflect/feas_probe.lean`).

## What is PROVED here (no `sorry`, `#print axioms` below).

* `qsCertSparse` — the 51 squares as SPARSE covectors `(coeff, [(coord, coeff)])`, generated
  deterministically from `compute/qslab_reflect/reflect_cert.json` by `compute/sparse_gram/gen_sparse.py`
  and cross-checked entry-by-entry against `QSlabReflect.qsSquares` (0 mismatches, in `gen_sparse.py`).
* `qsCertSparse_faithful` — **FAITHFULNESS TIE (kernel `decide`, axiom-standard).**
  `denseCert qsCertSparse = QSlabReflect.qsSquares`: the sparse covectors accumulate EXACTLY to the
  prosecuted dense `qsSquares` covectors.  This is the per-coordinate check (≤10-term covectors), which
  DOES `decide` fast — unlike the `80×80 = 6400`-entry dense Gram, which does not.  So the sparse cert
  is the SAME object as `qsSquares`, tied in-kernel, not merely by an external script.
* `qs_hpos_sparse` — all 51 coefficients `≥ 0` (`decide`).
* `qsSparse_nonneg` — **THE GRAM-FREE POSITIVITY (the payoff).**  `0 ≤ sosQuadValue (cast) B` for every
  real free-cell assignment `B`, by the reusable `sosQuadValue_nonneg` — term-by-term `sq_nonneg`, no
  dense Gram formed, no `decide` over any `80×80` enumeration, size-independent.
* `qsSparse_eq_sosVal` — the sparse SOS value EQUALS the exact SOS value object
  `sosVal (qsSquares.map castSq)` that the dense route (`QSlabReflect.qs_reflect`) is stated against.
  So the sparse route computes the identical value the dense route defines, but its positivity is
  proved WITHOUT the un-decidable `hgram`.

## FAITHFULNESS CAVEAT (unchanged from `QSlabReflect`; §LEAN-D "wrong object").

⚠ CORRECTED 2026-07-25 (main-loop-verified, commit 85a829c1): `qsCertSparse` is a **Tp-CERTIFICATE, NOT a
T-certificate**. Measured exactly (`compute/qslab_energy/decisive.py`, residual 0): `sosQuadValue
qsCertSparse = 128·(2·Q0 + ¼·Slab0)`, i.e. its implied Gram is `Tp = T + (1/24)·Top_M − (3/2)·Blk_M` (the
Top/Blk terms CANCEL inside the SOS). So `qsSparse_nonneg` delivers only `0 ≤ 2·Q0 + ¼·Slab0` — which is
**TRIVIALLY TRUE** (`coarseQEnergy`/`slabCurlEnergy` ARE sums of squares; the tree already has
`Lemma24Assembly` `hQ : 0 ≤ coarseQEnergy`). It does **NOT** bound `LocalGeomBackward0`, whose `−(1/24)·Top0`
term makes it not term-by-term nonneg and whose positivity (the load-bearing content of Lemma 2.4) needs
`T ⪰ 0`, not `Tp ⪰ 0`.  The correct discharge object is the **56-square `cert_backward.json`** (a genuine
T-cert: `sosQuadValue backCert = LocalGeomBackward0` exactly, weights > 0), whose Lean discharge needs the
dense-Gram reflection `gram backCert = T` + the 4-energy expansion `[RES-GEOM-REINDEX]` + transport — NOT
this covector-faithful shortcut. The GENERIC `RatSOSEval.sosQuadValue_nonneg` bridge remains correct and
reusable; only its application to `qsCertSparse` here certifies the trivial positivity.

⚠ UPDATE 2026-07-25 (`compute/tcert/`): the genuine 56-square T-cert's gram-free SOS positivity is now
built in `AdalyFormal.Balaban.BackwardTCert` (`backTSparse_nonneg`, axiom-clean) via the SAME
`sosQuadValue_nonneg` bridge — so the T-cert side needs NO dense `gram backCert = T` after all.  MEASURED
(`characterize_AB.py`): the dense-Gram reflection's ARITHMETIC kernel-checks in 3.63 s
(`backcert_gram_kernel_check.lean`, mutation fails), but its SOUND wiring through `RatSOSEval.gram` is
NOT `rfl`-able (naive `∀ a b, gram = T` timed out > 500 s at 56-square scale, `gram_probe.lean`); the
sparse route in `BackwardTCert` bypasses it.  The SOLE remaining wall for the ell=2 milestone is
`[RES-GEOM-REINDEX]` piece (ii) — tying `freecoord B` to `LocalGeomBackward0` — common to BOTH the (A)
dense and (B) covector-faithful representations (B exists: range(T) ⊆ span(energy forms), rank 56, but
its 19 energy-form relations give it no advantage over (A)). -/

namespace SparseGram

open RatSOSEval

/-- The 51 Q+Slab squares as SPARSE covectors `(coeff, [(coord, coeff)])`,
generated deterministically from `compute/qslab_reflect/reflect_cert.json`
(`compute/sparse_gram/gen_sparse.py`), cross-checked entry-by-entry against
`QSlabReflect.qsSquares` (0 mismatches).  Same prosecuted data, covector-faithful form. -/
def qsCertSparse : List (ℤ × List (Fin 80 × ℤ)) := [
  (4, [((64 : Fin 80), (1 : ℤ)), ((67 : Fin 80), (1 : ℤ)), ((71 : Fin 80), (1 : ℤ)), ((74 : Fin 80), (1 : ℤ))]),  -- Q line form 0
  (1, [((12 : Fin 80), (2 : ℤ)), ((14 : Fin 80), (2 : ℤ)), ((18 : Fin 80), (1 : ℤ)), ((21 : Fin 80), (1 : ℤ)), ((41 : Fin 80), (1 : ℤ)), ((44 : Fin 80), (1 : ℤ)), ((48 : Fin 80), (2 : ℤ)), ((51 : Fin 80), (2 : ℤ))]),  -- Q line form 1
  (1, [((1 : Fin 80), (2 : ℤ)), ((3 : Fin 80), (1 : ℤ)), ((7 : Fin 80), (1 : ℤ)), ((9 : Fin 80), (2 : ℤ)), ((19 : Fin 80), (1 : ℤ)), ((25 : Fin 80), (1 : ℤ)), ((28 : Fin 80), (2 : ℤ)), ((31 : Fin 80), (1 : ℤ)), ((34 : Fin 80), (1 : ℤ)), ((37 : Fin 80), (2 : ℤ))]),  -- Q line form 2
  (32, [((65 : Fin 80), (1 : ℤ))]),  -- Slab curl form 3
  (32, [((66 : Fin 80), (1 : ℤ))]),  -- Slab curl form 4
  (32, [((68 : Fin 80), (1 : ℤ))]),  -- Slab curl form 5
  (32, [((59 : Fin 80), (-1 : ℤ)), ((69 : Fin 80), (1 : ℤ))]),  -- Slab curl form 6
  (32, [((60 : Fin 80), (-1 : ℤ)), ((72 : Fin 80), (1 : ℤ))]),  -- Slab curl form 7
  (32, [((61 : Fin 80), (-1 : ℤ)), ((73 : Fin 80), (1 : ℤ))]),  -- Slab curl form 8
  (32, [((62 : Fin 80), (-1 : ℤ)), ((75 : Fin 80), (1 : ℤ))]),  -- Slab curl form 9
  (32, [((63 : Fin 80), (-1 : ℤ)), ((76 : Fin 80), (1 : ℤ))]),  -- Slab curl form 10
  (32, [((64 : Fin 80), (1 : ℤ)), ((65 : Fin 80), (-1 : ℤ)), ((71 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 11
  (32, [((64 : Fin 80), (1 : ℤ)), ((66 : Fin 80), (-1 : ℤ)), ((67 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 12
  (32, [((67 : Fin 80), (1 : ℤ)), ((68 : Fin 80), (-1 : ℤ)), ((74 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 13
  (32, [((0 : Fin 80), (1 : ℤ)), ((67 : Fin 80), (1 : ℤ)), ((69 : Fin 80), (-1 : ℤ)), ((70 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 14
  (32, [((2 : Fin 80), (1 : ℤ)), ((71 : Fin 80), (1 : ℤ)), ((72 : Fin 80), (-1 : ℤ)), ((78 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 15
  (32, [((3 : Fin 80), (1 : ℤ)), ((71 : Fin 80), (1 : ℤ)), ((73 : Fin 80), (-1 : ℤ)), ((74 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 16
  (32, [((4 : Fin 80), (1 : ℤ)), ((74 : Fin 80), (1 : ℤ)), ((75 : Fin 80), (-1 : ℤ)), ((79 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 17
  (32, [((5 : Fin 80), (1 : ℤ)), ((74 : Fin 80), (1 : ℤ)), ((76 : Fin 80), (-1 : ℤ)), ((77 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 18
  (32, [((41 : Fin 80), (1 : ℤ))]),  -- Slab curl form 19
  (32, [((13 : Fin 80), (1 : ℤ))]),  -- Slab curl form 20
  (32, [((44 : Fin 80), (1 : ℤ))]),  -- Slab curl form 21
  (32, [((11 : Fin 80), (-1 : ℤ)), ((15 : Fin 80), (1 : ℤ))]),  -- Slab curl form 22
  (32, [((12 : Fin 80), (-1 : ℤ)), ((48 : Fin 80), (1 : ℤ))]),  -- Slab curl form 23
  (32, [((12 : Fin 80), (1 : ℤ)), ((13 : Fin 80), (-1 : ℤ)), ((14 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 24
  (32, [((14 : Fin 80), (-1 : ℤ)), ((51 : Fin 80), (1 : ℤ))]),  -- Slab curl form 25
  (32, [((0 : Fin 80), (1 : ℤ)), ((14 : Fin 80), (1 : ℤ)), ((15 : Fin 80), (-1 : ℤ)), ((16 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 26
  (32, [((40 : Fin 80), (1 : ℤ)), ((41 : Fin 80), (-1 : ℤ)), ((47 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 27
  (32, [((41 : Fin 80), (1 : ℤ)), ((42 : Fin 80), (-1 : ℤ)), ((44 : Fin 80), (-1 : ℤ)), ((49 : Fin 80), (1 : ℤ))]),  -- Slab curl form 28
  (32, [((43 : Fin 80), (1 : ℤ)), ((44 : Fin 80), (-1 : ℤ)), ((50 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 29
  (32, [((44 : Fin 80), (1 : ℤ)), ((45 : Fin 80), (-1 : ℤ)), ((46 : Fin 80), (-1 : ℤ)), ((52 : Fin 80), (1 : ℤ))]),  -- Slab curl form 30
  (32, [((17 : Fin 80), (-1 : ℤ)), ((47 : Fin 80), (1 : ℤ)), ((48 : Fin 80), (-1 : ℤ)), ((57 : Fin 80), (1 : ℤ))]),  -- Slab curl form 31
  (32, [((19 : Fin 80), (1 : ℤ)), ((48 : Fin 80), (1 : ℤ)), ((49 : Fin 80), (-1 : ℤ)), ((51 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 32
  (32, [((20 : Fin 80), (-1 : ℤ)), ((50 : Fin 80), (1 : ℤ)), ((51 : Fin 80), (-1 : ℤ)), ((58 : Fin 80), (1 : ℤ))]),  -- Slab curl form 33
  (32, [((22 : Fin 80), (1 : ℤ)), ((51 : Fin 80), (1 : ℤ)), ((52 : Fin 80), (-1 : ℤ)), ((53 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 34
  (32, [((25 : Fin 80), (1 : ℤ))]),  -- Slab curl form 35
  (32, [((7 : Fin 80), (1 : ℤ))]),  -- Slab curl form 36
  (32, [((1 : Fin 80), (-1 : ℤ)), ((28 : Fin 80), (1 : ℤ))]),  -- Slab curl form 37
  (32, [((1 : Fin 80), (-1 : ℤ)), ((9 : Fin 80), (1 : ℤ))]),  -- Slab curl form 38
  (32, [((7 : Fin 80), (-1 : ℤ)), ((34 : Fin 80), (1 : ℤ))]),  -- Slab curl form 39
  (32, [((6 : Fin 80), (1 : ℤ)), ((7 : Fin 80), (-1 : ℤ)), ((8 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 40
  (32, [((9 : Fin 80), (-1 : ℤ)), ((37 : Fin 80), (1 : ℤ))]),  -- Slab curl form 41
  (32, [((2 : Fin 80), (-1 : ℤ)), ((8 : Fin 80), (1 : ℤ)), ((9 : Fin 80), (-1 : ℤ)), ((10 : Fin 80), (1 : ℤ))]),  -- Slab curl form 42
  (32, [((23 : Fin 80), (1 : ℤ)), ((25 : Fin 80), (-1 : ℤ)), ((26 : Fin 80), (-1 : ℤ))]),  -- Slab curl form 43
  (32, [((24 : Fin 80), (1 : ℤ)), ((25 : Fin 80), (-1 : ℤ)), ((27 : Fin 80), (-1 : ℤ)), ((34 : Fin 80), (1 : ℤ))]),  -- Slab curl form 44
  (32, [((17 : Fin 80), (-1 : ℤ)), ((26 : Fin 80), (1 : ℤ)), ((28 : Fin 80), (-1 : ℤ)), ((54 : Fin 80), (1 : ℤ))]),  -- Slab curl form 45
  (32, [((18 : Fin 80), (-1 : ℤ)), ((27 : Fin 80), (1 : ℤ)), ((28 : Fin 80), (-1 : ℤ)), ((37 : Fin 80), (1 : ℤ))]),  -- Slab curl form 46
  (32, [((32 : Fin 80), (1 : ℤ)), ((34 : Fin 80), (-1 : ℤ)), ((35 : Fin 80), (-1 : ℤ)), ((55 : Fin 80), (1 : ℤ))]),  -- Slab curl form 47
  (32, [((33 : Fin 80), (1 : ℤ)), ((34 : Fin 80), (-1 : ℤ)), ((36 : Fin 80), (-1 : ℤ)), ((38 : Fin 80), (1 : ℤ))]),  -- Slab curl form 48
  (32, [((29 : Fin 80), (-1 : ℤ)), ((35 : Fin 80), (1 : ℤ)), ((37 : Fin 80), (-1 : ℤ)), ((56 : Fin 80), (1 : ℤ))]),  -- Slab curl form 49
  (32, [((30 : Fin 80), (-1 : ℤ)), ((36 : Fin 80), (1 : ℤ)), ((37 : Fin 80), (-1 : ℤ)), ((39 : Fin 80), (1 : ℤ))])   -- Slab curl form 50
]

/-- **FAITHFULNESS TIE (kernel `decide`, axiom-standard).** The sparse covectors accumulate exactly to
the prosecuted dense `qsSquares` covectors: `denseCert qsCertSparse = QSlabReflect.qsSquares`.  This is
the per-coordinate check (≤10 nonzeros per covector) — it `decide`s fast, unlike the `6400`-entry dense
Gram.  So `qsCertSparse` IS `qsSquares`, tied in the kernel. -/
theorem qsCertSparse_faithful : denseCert qsCertSparse = QSlabReflect.qsSquares := by decide

/-- All 51 sparse coefficients are nonnegative. -/
theorem qs_hpos_sparse : ∀ t ∈ qsCertSparse, 0 ≤ t.1 := by decide

theorem qs_hpos_sparse_cast : ∀ t ∈ qsCertSparse.map castSparse, 0 ≤ t.1 := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  show (0:ℝ) ≤ ((s.1 : ℤ) : ℝ)
  exact_mod_cast qs_hpos_sparse s hs

/-- **THE GRAM-FREE POSITIVITY (PROVED, no `sorry`).** For every real free-cell assignment `B`, the
exact Q+Slab SOS value is nonnegative — proved TERM-BY-TERM via `sosQuadValue_nonneg` (`sq_nonneg`),
with NO dense `80×80` Gram formed and NO `decide` over any Gram enumeration.  This is the reusable
covector-faithful bridge instantiated: it discharges the positivity that
`QSlabReflect.qs_reflect_nonneg` could only state CONDITIONALLY on the un-decidable dense-Gram
hypothesis `hgram`. -/
theorem qsSparse_nonneg (B : Fin 80 → ℝ) :
    0 ≤ sosQuadValue (qsCertSparse.map castSparse) B :=
  sosQuadValue_nonneg _ qs_hpos_sparse_cast B

/-- **COHERENCE WITH THE DENSE ROUTE (PROVED).** The sparse SOS value equals the exact value object
`sosVal (qsSquares.map castSq)` that `QSlabReflect.qs_reflect` is stated against — so the sparse route
computes the identical SOS value the dense route defines, but proves its positivity WITHOUT `hgram`. -/
theorem qsSparse_eq_sosVal (B : Fin 80 → ℝ) :
    sosQuadValue (qsCertSparse.map castSparse) B
      = sosVal (QSlabReflect.qsSquares.map castSq) B := by
  rw [sosQuadValue_eq_sosVal, denseCert_castSparse, qsCertSparse_faithful]

#print axioms qsCertSparse_faithful
#print axioms qs_hpos_sparse
#print axioms qsSparse_nonneg
#print axioms qsSparse_eq_sosVal

end SparseGram
