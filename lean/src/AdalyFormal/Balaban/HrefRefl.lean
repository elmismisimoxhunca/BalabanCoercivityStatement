import AdalyFormal.Balaban.BackwardTCert
import AdalyFormal.Balaban.SparseGram
import AdalyFormal.Balaban.QSlabExpand
import AdalyFormal.Balaban.HrefBlk

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8000000

/-! # `HrefRefl` — the SOS-basis reflection wall `hrefl` of the `U=1 ℓ=2` `Href` identity, PROVED.

`HrefReduction.href_of_QSlab_refl` reduces the reference-block SOS identity `Href` to TWO precisely
typed hypotheses: `hQS` (the Q+Slab reindex, a separate lane) and `hrefl` (the SOS-basis reflection).
This module DISCHARGES `hrefl` (`hrefl_proved` below), axiom-clean, for the explicit integer scale
`W = Wint` (`Wpos : 0 < (Wint : ℝ)`).

## The statement (exactly `HrefReduction`'s `hrefl` at `W = Wint`).
For every `x : Fin 80 → ℝ`,
  `sosQuadValue (backCertSparse.map castSparse) x
     = Wint · ( (1/128)·sosQuadValue (qsCertSparse.map castSparse) x
                − (1/3)(1/2³)·∑_{i∈topIds} xᵢ² + 6(1/2²)·∑_{i∈blkIds} xᵢ² )`.

## How it is proved (sound, no `native_decide`, no `sorry`, no new `axiom`).
Both sides are quadratic forms in `x`.  Via the proved `RatSOSEval` bridges
(`sosQuadValue_eq_gramQuad`, `denseCert_castSparse`, `gram_cast`) each `sosQuadValue` becomes the
quadratic form of the ℤ→ℝ cast of the IMPLIED INTEGER Gram `gram (denseCert cert)`, and each diagonal
energy `∑_{i∈S} xᵢ²` becomes the quadratic form of the diagonal indicator matrix `Dind S` (`diag_sum`).
The whole identity then reduces to the ENTRYWISE integer identity (`hINT`)
  `384·gram_bc a b = Wint·(3·gram_qs a b − 16·Dind topIds a b + 576·Dind blkIds a b)`  (∀ a b : Fin 80),
which is discharged by a single STRICT-KERNEL `rfl` over the real `RatSOSEval.gram` of the real
`backCertSparse`/`qsCertSparse` (NO emitted leaves — the leaves are the actual covector products, so
the tie is SOUND, not a disconnected arithmetic file).  `1/24 = 16/384`, `3/2 = 576/384` and
`1/128 = 3/384` (`starR`) convert the cleared integer identity back to the real one.

## PERFORMANCE (measured, `compute/href_refl/`, Lean v4.31.0).
The decisive `hINTbool_true` `rfl` is MEASURED at ~320 s (`compute/href_refl/measure_naive.out`,
`WALL=320.35 s`, `#print axioms` clean).  This is under the > 500 s wall of the naive dense
`∀ a b, gram backCertI a b = T a b` (`compute/tcert/gram_probe.out`, EXIT 124, WALL 500.78 s) but
over the ~60 s target.  The bottleneck is the `6400 × (56 + 51)` kernel re-evaluations of `scovDense`
+ 80-digit `Int` products — the ENTRY-COUNT × SQUARE-COUNT, NOT the sum-DEPTH (56, shallow) that the
`RatSOSEval.STree` balanced tree accelerates; so STree gives no speedup at this square count.  A
`< 60 s` discharge needs nonzero-leaf enumeration with a completeness proof (off-support Gram
vanishing) — the deferred `[RES-CERT-KERNEL-REFLECT]` wiring — which this SOUND-but-slower route does
not require.  `Wint` is a genuine 80-digit integer (`compute/href_refl/analyze.py`, `PYTHONHASHSEED=0`,
`W.denominator = 1`), reflecting the intrinsic 27-digit weights of the rank-56 backward T-cert. -/

namespace AdalyFormal.Balaban.HrefRefl

open Finset
open RatSOSEval
open QSlabExpand (topIds)
open HrefBlk (blkIds)

/-- The explicit integer scale `W` of the reflection (`compute/href_refl/analyze.py`: exact,
`W.denominator = 1`, `W > 0`; 80 digits, reflecting the rank-56 backward T-cert's intrinsic weights). -/
def Wint : ℤ := 10019534471711313938540957458953612074523334709426554662881004453177611542738560

/-- `0 < W` (the witness `c = 1/W ≥ 0` in `href_of_QSlab_refl` needs this). -/
theorem Wpos : (0 : ℝ) < (Wint : ℝ) := by
  have h : (0 : ℤ) < Wint := by decide
  exact_mod_cast h

/-- Diagonal indicator matrix for a coordinate set `S`: `1` on `(a,a)` with `a ∈ S`, else `0`. -/
def Dind (S : Finset (Fin 80)) (a b : Fin 80) : ℤ := if a = b ∧ a ∈ S then 1 else 0

/-- The implied INTEGER Gram of the backward T-cert (spec, never densely materialized in the value). -/
abbrev Gbc (a b : Fin 80) : ℤ := gram (denseCert BackwardTCert.backCertSparse) a b
/-- The implied INTEGER Gram of the Q+Slab cert. -/
abbrev Gqs (a b : Fin 80) : ℤ := gram (denseCert SparseGram.qsCertSparse) a b

/-- The entrywise integer identity as a single kernel-checkable `Bool`. -/
def hINTbool : Bool :=
  (List.finRange 80).all (fun a => (List.finRange 80).all (fun b =>
    384 * Gbc a b == Wint * (3 * Gqs a b - 16 * Dind topIds a b + 576 * Dind blkIds a b)))

/-- **THE INTEGER CORE (STRICT KERNEL `rfl`, ~320 s, axiom-clean).**  For the REAL `RatSOSEval.gram`
of the REAL `backCertSparse`/`qsCertSparse`, every entry satisfies the cleared reflection identity.
The leaves the kernel sums are the actual covector products (`scovDense`), so this ties the arithmetic
to the certificates soundly (unlike `compute/tcert/backcert_gram_kernel_check.lean`, whose leaves are
emitted literals). -/
theorem hINTbool_true : hINTbool = true := by rfl

/-- The entrywise integer identity, extracted from `hINTbool_true`. -/
theorem hINT (a b : Fin 80) :
    384 * Gbc a b = Wint * (3 * Gqs a b - 16 * Dind topIds a b + 576 * Dind blkIds a b) := by
  have h := hINTbool_true
  unfold hINTbool at h
  rw [List.all_eq_true] at h
  have ha := h a (List.mem_finRange a)
  rw [List.all_eq_true] at ha
  exact eq_of_beq (ha b (List.mem_finRange b))

/-- The real entrywise identity (★ℝ) from the integer core: `1/24 = 16/384`, `3/2 = 576/384`,
`1/128 = 3/384`. -/
theorem starR (a b : Fin 80) :
    (Gbc a b : ℝ)
      = (Wint : ℝ) * ((1/128) * (Gqs a b : ℝ)
          - (1/24) * (Dind topIds a b : ℝ) + (3/2) * (Dind blkIds a b : ℝ)) := by
  have h := hINT a b
  have hR : (384 : ℝ) * (Gbc a b : ℝ)
      = (Wint : ℝ) * (3 * (Gqs a b : ℝ) - 16 * (Dind topIds a b : ℝ) + 576 * (Dind blkIds a b : ℝ)) := by
    exact_mod_cast h
  have e : (Wint : ℝ) * ((1/128) * (Gqs a b : ℝ)
            - (1/24) * (Dind topIds a b : ℝ) + (3/2) * (Dind blkIds a b : ℝ))
        = (1/384) * ((Wint : ℝ) * (3 * (Gqs a b : ℝ)
            - 16 * (Dind topIds a b : ℝ) + 576 * (Dind blkIds a b : ℝ))) := by ring
  rw [e, ← hR]; ring

/-- A diagonal energy `∑_{i∈S} xᵢ²` as the quadratic form of the indicator matrix `Dind S`. -/
theorem diag_sum (S : Finset (Fin 80)) (x : Fin 80 → ℝ) :
    (∑ i ∈ S, (x i)^2) = ∑ a, ∑ b, ((Dind S a b : ℤ) : ℝ) * (x a * x b) := by
  have hb : ∀ a : Fin 80, (∑ b, ((Dind S a b : ℤ) : ℝ) * (x a * x b))
        = if a ∈ S then (x a)^2 else 0 := by
    intro a
    unfold Dind
    have hsplit : ∀ b : Fin 80, (((if a = b ∧ a ∈ S then (1:ℤ) else 0) : ℤ) : ℝ) * (x a * x b)
        = if a ∈ S then ((if a = b then (1:ℝ) else 0) * (x a * x b)) else 0 := by
      intro b
      by_cases hmem : a ∈ S <;> by_cases hab : a = b <;> simp [hmem, hab]
    rw [Finset.sum_congr rfl (fun b _ => hsplit b)]
    by_cases hmem : a ∈ S
    · simp only [hmem, if_true, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ a (fun b => x a * x b), if_pos (Finset.mem_univ a)]
      ring
    · simp [hmem]
  rw [Finset.sum_congr rfl (fun a _ => hb a)]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- ℤ→ℝ bridge for the backCert Gram. -/
theorem gcast_bc (a b : Fin 80) :
    gram (denseCert (BackwardTCert.backCertSparse.map castSparse)) a b = ((Gbc a b : ℤ) : ℝ) := by
  rw [denseCert_castSparse, gram_cast]

/-- ℤ→ℝ bridge for the qsCert Gram. -/
theorem gcast_qs (a b : Fin 80) :
    gram (denseCert (SparseGram.qsCertSparse.map castSparse)) a b = ((Gqs a b : ℤ) : ℝ) := by
  rw [denseCert_castSparse, gram_cast]

/-- **`hrefl` PROVED (no `sorry`, no `native_decide`, no new `axiom`; `#print axioms` below).**
The SOS-basis reflection identity of `HrefReduction`, at the explicit scale `W = Wint`. -/
theorem hrefl_proved (x : Fin 80 → ℝ) :
    sosQuadValue (BackwardTCert.backCertSparse.map castSparse) x
      = (Wint : ℝ) * ((1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) x
              - (1 / 3) * (1 / ((2 : ℕ) : ℝ) ^ 3) * (∑ i ∈ topIds, (x i) ^ 2)
              + 6 * (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ i ∈ blkIds, (x i) ^ 2)) := by
  rw [sosQuadValue_eq_gramQuad (BackwardTCert.backCertSparse.map castSparse) x,
      sosQuadValue_eq_gramQuad (SparseGram.qsCertSparse.map castSparse) x,
      diag_sum topIds x, diag_sum blkIds x]
  simp only [gcast_bc, gcast_qs]
  have c1 : (1 / 3) * (1 / ((2 : ℕ) : ℝ) ^ 3) = (1/24 : ℝ) := by norm_num
  have c2 : (6 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 2) = (3/2 : ℝ) := by norm_num
  rw [c1, c2, mul_add, mul_sub]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [starR a b]
  ring

#print axioms hrefl_proved

end AdalyFormal.Balaban.HrefRefl
