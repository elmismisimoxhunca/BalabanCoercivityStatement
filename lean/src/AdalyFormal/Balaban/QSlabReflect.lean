import AdalyFormal.Balaban.RatSOSEval

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `QSlabReflect` — the reference-block `ell=2` Q+Slab energies as an explicit free-cell
sum-of-squares, and its kernel-reflection interface.

This module carries the CONCRETE reflectable data for the off-diagonal wall of piece (ii) of
`[RES-GEOM-REINDEX]`: the two off-diagonal reference-block energies

    `Q0    = ∑_μ (lineCoarseRestrict 2 B (⟨prevSite μ⟩, μ))²`        (scale `2`,   3 line forms)
    `Slab0 = ∑_μ ∑_{p∈slab(prevSite μ,μ)} (curlValue B p)²`          (scale `1/4`, 48 curl forms)

expressed, on the admissible subspace (pinned bonds dropped), as a nonnegative-coefficient
sum-of-squares of `51 = 3 + 48` explicit rational LINEAR forms in the 80 free-cell coordinates
`v_i = B(freeCellBond i)`:

    `2·Q0 + (1/4)·Slab0  =  ∑ₐ dₐ (Lₐ · v)²  =  ⟨v, T' v⟩`,   `T' = T + (1/24)·Top_M − (3/2)·Blk_M`.

`Top_M`, `Blk_M` are the DIAGONAL indicator matrices on `QSlabExpand.topIds` (12 coords) and the 5
free in-block coords `{3,18,19,21,31}`.  Top's free-cell reindex IS proved
(`QSlabExpand.topFace_total`).  Blk's is NOT yet: `EnergyEval.inBlock_energy_full_drop` proves only
the admissibility DROP (the 7 pinned in-block bonds vanish), not the reindex of the 5 surviving bonds
to the cert free-coords `{3,18,19,21,31}` — that is the Blk analogue of `topFace_total`, unbuilt (the
compute verifies the indices, residual 0).  With BOTH Top and Blk reindexed, this reflection would give
the full reference-block identity `2Q0 + ¼Slab0 − (1/24)Top0 + (3/2)Blk0 = ⟨v, T v⟩`.

## What is EXACT (compute/qslab_reflect/extract_reflect.py, exact ℚ, PYTHONHASHSEED=0, N∈{6,8}).

The integer-scaled Gram identity `∑ₐ wₐ Lₐ[a] Lₐ[b] = 128·T'[a][b]` (`W = 128`, all `wₐ ≥ 0`,
628 leaf multiply-adds, max covector nnz 10) holds with residual 0 over all 520 nonzero entries,
size-uniform N∈{6,8}; four mutation controls (drop a curl form, mis-scale Q, flip the Top sign, drop
the Blk correction) each break it.  This is the data `qsSquares` / and its target `T'` below.

## FAITHFULNESS CAVEAT (read before consuming — §LEAN-D "wrong object" surface).

`qsSquares` is the exact-ℚ data EXTRACTED from `compute/qslab_reflect/extract_reflect.py`; it is NOT
proved in Lean to equal the actual energies `2·Q0 + ¼·Slab0` in free coordinates.  That identification
— that `Lₐ · v(B)` IS the line-integral / curl form of the energy on the admissible subspace — is
`[RES-GEOM-REINDEX]` for Q/Slab (unbuilt, see below).  So nothing here yet asserts that `qsSquares`
denotes the energies; it asserts only the self-contained algebra of the listed integer forms.

## What is PROVED here (no `sorry`, axiom-clean).

* `qsSquares` — the 51 integer squares `(wₐ, Lₐ)` (`Lₐ : Fin 80 → ℤ`, sparse if-chain), first 3 = the
  Q line forms, next 48 = the Slab curl forms (compute-extracted; faithfulness caveat above).
* `qs_hpos` — all 51 coefficients are `≥ 0` (`by decide`; the PSD-corollary hypothesis).
* `qs_reflect` / `qs_reflect_nonneg` — the REFLECTION INTERFACE: for ANY integer target `T` and ANY
  real assignment `x`, from the integer Gram identity `hgram : ∀ a b, gram qsSquares a b = T a b` the
  `T`-quadratic form of `x` EQUALS the (cast) SOS value `sosVal (qsSquares.map castSq) x` and is `≥ 0`.
  Direct specialisation of `RatSOSEval.quadForm_eq_sos_of_intGram` / `quadForm_nonneg_of_intGram` to
  the concrete Q+Slab forms (same conditional-on-`hgram` shape as
  `GeomGlobal.freecell_quadForm_nonneg`).

## The named residual `[RES-QSLAB-GRAM]` (MEASURED — the reflection does NOT remove it).

Discharging `hgram` for the concrete `T' = 128·T'`-target is the last mile.  The ARITHMETIC half is
trivial: the raw-integer balanced-tree identity `∑ₐ wₐ Lₐ[a] Lₐ[b] = 128 T'[a][b]` kernel-checks by
`rfl` in ~8 s, axiom-clean, no `native_decide` (`compute/qslab_reflect/arith_cert.lean`,
`QSArith.certOK`).  But that check does NOT mention `RatSOSEval.gram` — the covectors are precomputed,
not reduced in-kernel.  The SEMANTIC identity `∀ a b, gram qsSquares a b = T' a b` (which DOES reduce
the covectors) does NOT kernel-check by `decide` in practical time: measured >7 min and killed for
BOTH the `![…]`-vector and the sparse if-chain covector representations, because the Fin-80 × Fin-80
= 6400-entry `∀`-enumeration reduces a 51-term `List.sum` per entry in the kernel
(`compute/qslab_reflect/feas_probe.lean`, `feas_probe2.lean`).  This is exactly the
`[RES-CERT-KERNEL-REFLECT]` "covector-faithful sparse-Gram wiring" the campaign already names as
unbuilt — the smaller 51-form Q+Slab instance confirms it: the reflection settles the arithmetic but
NOT the semantic bridge.  Its consumer (a full piece (ii)) SEPARATELY needs the per-energy free-cell
evaluation `[RES-GEOM-REINDEX]` (Q: 3 line forms with `prevSite μ` torus-wrap and pinned-bond drops;
Slab: 48 curl forms) — the analogue of the proved `QSlabExpand.topFace_*`, unbuilt for Q/Slab. -/

namespace QSlabReflect

open RatSOSEval

def qsSquares : List (ℤ × (Fin 80 → ℤ)) := [
  (4, fun i : Fin 80 => (if i.val = 64 then 1 else (if i.val = 67 then 1 else (if i.val = 71 then 1 else (if i.val = 74 then 1 else 0))))),  -- Q line form 0
  (1, fun i : Fin 80 => (if i.val = 12 then 2 else (if i.val = 14 then 2 else (if i.val = 18 then 1 else (if i.val = 21 then 1 else (if i.val = 41 then 1 else (if i.val = 44 then 1 else (if i.val = 48 then 2 else (if i.val = 51 then 2 else 0))))))))),  -- Q line form 1
  (1, fun i : Fin 80 => (if i.val = 1 then 2 else (if i.val = 3 then 1 else (if i.val = 7 then 1 else (if i.val = 9 then 2 else (if i.val = 19 then 1 else (if i.val = 25 then 1 else (if i.val = 28 then 2 else (if i.val = 31 then 1 else (if i.val = 34 then 1 else (if i.val = 37 then 2 else 0))))))))))),  -- Q line form 2
  (32, fun i : Fin 80 => (if i.val = 65 then 1 else 0)),  -- Slab curl form 3
  (32, fun i : Fin 80 => (if i.val = 66 then 1 else 0)),  -- Slab curl form 4
  (32, fun i : Fin 80 => (if i.val = 68 then 1 else 0)),  -- Slab curl form 5
  (32, fun i : Fin 80 => (if i.val = 59 then (-1) else (if i.val = 69 then 1 else 0))),  -- Slab curl form 6
  (32, fun i : Fin 80 => (if i.val = 60 then (-1) else (if i.val = 72 then 1 else 0))),  -- Slab curl form 7
  (32, fun i : Fin 80 => (if i.val = 61 then (-1) else (if i.val = 73 then 1 else 0))),  -- Slab curl form 8
  (32, fun i : Fin 80 => (if i.val = 62 then (-1) else (if i.val = 75 then 1 else 0))),  -- Slab curl form 9
  (32, fun i : Fin 80 => (if i.val = 63 then (-1) else (if i.val = 76 then 1 else 0))),  -- Slab curl form 10
  (32, fun i : Fin 80 => (if i.val = 64 then 1 else (if i.val = 65 then (-1) else (if i.val = 71 then (-1) else 0)))),  -- Slab curl form 11
  (32, fun i : Fin 80 => (if i.val = 64 then 1 else (if i.val = 66 then (-1) else (if i.val = 67 then (-1) else 0)))),  -- Slab curl form 12
  (32, fun i : Fin 80 => (if i.val = 67 then 1 else (if i.val = 68 then (-1) else (if i.val = 74 then (-1) else 0)))),  -- Slab curl form 13
  (32, fun i : Fin 80 => (if i.val = 0 then 1 else (if i.val = 67 then 1 else (if i.val = 69 then (-1) else (if i.val = 70 then (-1) else 0))))),  -- Slab curl form 14
  (32, fun i : Fin 80 => (if i.val = 2 then 1 else (if i.val = 71 then 1 else (if i.val = 72 then (-1) else (if i.val = 78 then (-1) else 0))))),  -- Slab curl form 15
  (32, fun i : Fin 80 => (if i.val = 3 then 1 else (if i.val = 71 then 1 else (if i.val = 73 then (-1) else (if i.val = 74 then (-1) else 0))))),  -- Slab curl form 16
  (32, fun i : Fin 80 => (if i.val = 4 then 1 else (if i.val = 74 then 1 else (if i.val = 75 then (-1) else (if i.val = 79 then (-1) else 0))))),  -- Slab curl form 17
  (32, fun i : Fin 80 => (if i.val = 5 then 1 else (if i.val = 74 then 1 else (if i.val = 76 then (-1) else (if i.val = 77 then (-1) else 0))))),  -- Slab curl form 18
  (32, fun i : Fin 80 => (if i.val = 41 then 1 else 0)),  -- Slab curl form 19
  (32, fun i : Fin 80 => (if i.val = 13 then 1 else 0)),  -- Slab curl form 20
  (32, fun i : Fin 80 => (if i.val = 44 then 1 else 0)),  -- Slab curl form 21
  (32, fun i : Fin 80 => (if i.val = 11 then (-1) else (if i.val = 15 then 1 else 0))),  -- Slab curl form 22
  (32, fun i : Fin 80 => (if i.val = 12 then (-1) else (if i.val = 48 then 1 else 0))),  -- Slab curl form 23
  (32, fun i : Fin 80 => (if i.val = 12 then 1 else (if i.val = 13 then (-1) else (if i.val = 14 then (-1) else 0)))),  -- Slab curl form 24
  (32, fun i : Fin 80 => (if i.val = 14 then (-1) else (if i.val = 51 then 1 else 0))),  -- Slab curl form 25
  (32, fun i : Fin 80 => (if i.val = 0 then 1 else (if i.val = 14 then 1 else (if i.val = 15 then (-1) else (if i.val = 16 then (-1) else 0))))),  -- Slab curl form 26
  (32, fun i : Fin 80 => (if i.val = 40 then 1 else (if i.val = 41 then (-1) else (if i.val = 47 then (-1) else 0)))),  -- Slab curl form 27
  (32, fun i : Fin 80 => (if i.val = 41 then 1 else (if i.val = 42 then (-1) else (if i.val = 44 then (-1) else (if i.val = 49 then 1 else 0))))),  -- Slab curl form 28
  (32, fun i : Fin 80 => (if i.val = 43 then 1 else (if i.val = 44 then (-1) else (if i.val = 50 then (-1) else 0)))),  -- Slab curl form 29
  (32, fun i : Fin 80 => (if i.val = 44 then 1 else (if i.val = 45 then (-1) else (if i.val = 46 then (-1) else (if i.val = 52 then 1 else 0))))),  -- Slab curl form 30
  (32, fun i : Fin 80 => (if i.val = 17 then (-1) else (if i.val = 47 then 1 else (if i.val = 48 then (-1) else (if i.val = 57 then 1 else 0))))),  -- Slab curl form 31
  (32, fun i : Fin 80 => (if i.val = 19 then 1 else (if i.val = 48 then 1 else (if i.val = 49 then (-1) else (if i.val = 51 then (-1) else 0))))),  -- Slab curl form 32
  (32, fun i : Fin 80 => (if i.val = 20 then (-1) else (if i.val = 50 then 1 else (if i.val = 51 then (-1) else (if i.val = 58 then 1 else 0))))),  -- Slab curl form 33
  (32, fun i : Fin 80 => (if i.val = 22 then 1 else (if i.val = 51 then 1 else (if i.val = 52 then (-1) else (if i.val = 53 then (-1) else 0))))),  -- Slab curl form 34
  (32, fun i : Fin 80 => (if i.val = 25 then 1 else 0)),  -- Slab curl form 35
  (32, fun i : Fin 80 => (if i.val = 7 then 1 else 0)),  -- Slab curl form 36
  (32, fun i : Fin 80 => (if i.val = 1 then (-1) else (if i.val = 28 then 1 else 0))),  -- Slab curl form 37
  (32, fun i : Fin 80 => (if i.val = 1 then (-1) else (if i.val = 9 then 1 else 0))),  -- Slab curl form 38
  (32, fun i : Fin 80 => (if i.val = 7 then (-1) else (if i.val = 34 then 1 else 0))),  -- Slab curl form 39
  (32, fun i : Fin 80 => (if i.val = 6 then 1 else (if i.val = 7 then (-1) else (if i.val = 8 then (-1) else 0)))),  -- Slab curl form 40
  (32, fun i : Fin 80 => (if i.val = 9 then (-1) else (if i.val = 37 then 1 else 0))),  -- Slab curl form 41
  (32, fun i : Fin 80 => (if i.val = 2 then (-1) else (if i.val = 8 then 1 else (if i.val = 9 then (-1) else (if i.val = 10 then 1 else 0))))),  -- Slab curl form 42
  (32, fun i : Fin 80 => (if i.val = 23 then 1 else (if i.val = 25 then (-1) else (if i.val = 26 then (-1) else 0)))),  -- Slab curl form 43
  (32, fun i : Fin 80 => (if i.val = 24 then 1 else (if i.val = 25 then (-1) else (if i.val = 27 then (-1) else (if i.val = 34 then 1 else 0))))),  -- Slab curl form 44
  (32, fun i : Fin 80 => (if i.val = 17 then (-1) else (if i.val = 26 then 1 else (if i.val = 28 then (-1) else (if i.val = 54 then 1 else 0))))),  -- Slab curl form 45
  (32, fun i : Fin 80 => (if i.val = 18 then (-1) else (if i.val = 27 then 1 else (if i.val = 28 then (-1) else (if i.val = 37 then 1 else 0))))),  -- Slab curl form 46
  (32, fun i : Fin 80 => (if i.val = 32 then 1 else (if i.val = 34 then (-1) else (if i.val = 35 then (-1) else (if i.val = 55 then 1 else 0))))),  -- Slab curl form 47
  (32, fun i : Fin 80 => (if i.val = 33 then 1 else (if i.val = 34 then (-1) else (if i.val = 36 then (-1) else (if i.val = 38 then 1 else 0))))),  -- Slab curl form 48
  (32, fun i : Fin 80 => (if i.val = 29 then (-1) else (if i.val = 35 then 1 else (if i.val = 37 then (-1) else (if i.val = 56 then 1 else 0))))),  -- Slab curl form 49
  (32, fun i : Fin 80 => (if i.val = 30 then (-1) else (if i.val = 36 then 1 else (if i.val = 37 then (-1) else (if i.val = 39 then 1 else 0)))))  -- Slab curl form 50
]

/-- All 51 sum-of-squares coefficients are nonnegative (PSD-corollary hypothesis). -/
theorem qs_hpos : ∀ s ∈ qsSquares, 0 ≤ s.1 := by decide

#print axioms qs_hpos

/-- **THE REFLECTION INTERFACE (PROVED, no `sorry`).** For any integer target `T` whose integer
Gram identity holds against the concrete Q+Slab forms, the real `T`-quadratic form of `x` equals the
cast SOS value of the 51 forms.  Specialisation of `RatSOSEval.quadForm_eq_sos_of_intGram`. -/
theorem qs_reflect (T : Fin 80 → Fin 80 → ℤ)
    (hgram : ∀ a b, gram qsSquares a b = T a b) (x : Fin 80 → ℝ) :
    ∑ a, ∑ b, ((T a b : ℤ) : ℝ) * (x a * x b) = sosVal (qsSquares.map castSq) x :=
  quadForm_eq_sos_of_intGram qsSquares T hgram x

#print axioms qs_reflect

/-- **THE REFLECTION INTERFACE — positivity (PROVED, no `sorry`).** …and the `T`-quadratic form is
nonnegative (the manifest positivity `2Q0 + ¼Slab0 ≥ 0` as a genuine sum of squares). -/
theorem qs_reflect_nonneg (T : Fin 80 → Fin 80 → ℤ)
    (hgram : ∀ a b, gram qsSquares a b = T a b) (x : Fin 80 → ℝ) :
    0 ≤ ∑ a, ∑ b, ((T a b : ℤ) : ℝ) * (x a * x b) :=
  quadForm_nonneg_of_intGram qsSquares qs_hpos T hgram x

#print axioms qs_reflect_nonneg

end QSlabReflect
