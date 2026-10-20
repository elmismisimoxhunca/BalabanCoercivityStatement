import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-! # `RatSOSEval` — a reusable, kernel-checkable exact-rational SOS evaluator (strict kernel).

This module provides the REUSABLE soundness core for discharging exact sum-of-squares certificates
of the form

    `M = ∑ᵢ dᵢ · vᵢ vᵢᵀ`   (a symmetric matrix `M` written as a coefficient-nonnegative Gram sum),

by a STRICT-KERNEL check (`rfl` / `decide` on a linear evaluator), with `native_decide` BANNED (L1).

## What is PROVED here (no `sorry`).

* `sosVal_eq_gramQuad` — the algebraic heart: for any finite family of squares
  `(dᵢ, covectorᵢ)` the SOS value `∑ᵢ dᵢ (⟨covᵢ, x⟩)²` equals the quadratic form `∑_{a,b} G_{ab} xₐx_b`
  of the IMPLIED Gram matrix `G_{ab} = ∑ᵢ dᵢ covᵢ(a) covᵢ(b)`.  Pure `Finset`/`List` algebra.
* `sosVal_nonneg`, `sosVal_cast_nonneg` — positivity from nonnegative coefficients.
* `gramQuad_eq_sos_of_eq`, `gramQuad_nonneg_of_eq` — if the implied Gram equals a target `M`, the
  `M`-quadratic form IS a nonnegative SOS.
* `gram_cast` — the ℤ→ℝ bridge: the real Gram of cast-from-ℤ data is the `Int.cast` of the integer
  Gram, so a checked INTEGER Gram identity transports to the real one (`Int.cast` is injective).
* `quadForm_nonneg_of_intGram` / `quadForm_eq_sos_of_intGram` — **the end-to-end interface**: from a
  nonneg-coefficient integer certificate whose (integer, kernel-checkable) Gram identity
  `∀ a b, gram sqsI a b = T a b` holds, the real quadratic form of `T` is a nonnegative SOS and equals
  the (real, cast) SOS value.  The ONLY hypothesis is the integer Gram identity.
* `STree`, `STree.eval_eq_leaves_sum` — a balanced-binary-tree integer evaluator whose kernel
  reduction is LINEAR (depth `O(log K)`, no deep left-nested spine), together with the generic lemma
  `eval = leaves.sum`.  This is the REFLECTION PRIMITIVE that makes the per-certificate integer sum
  `gram sqsI a b` kernel-reduce fast (a left-nested `List.sum` fold is super-linear in the kernel;
  a balanced tree is linear — measured, see `compute/rat_sos_eval/FEASIBILITY.md`).

## Feasibility (MEASURED — corrects the earlier `[RES-CERT-KERNEL-REFLECT]` "infeasible" verdict).

The `ℓ=2` geometry certificate (`compute/blochpsd/cert_data.json`, 1243 squares, 1296 nonzero Gram
entries, integer-scaled by `W = 921600`, 26808 leaf multiply-adds) kernel-checks by `rfl` in **~35 s**
with `#print axioms` reporting NO axioms (`compute/rat_sos_eval/`).  The prior "does not kernel-check"
measurement used Mathlib `List.filter/map/sum` inside `decide` over a LEFT-NESTED fold — super-linear
(`~K^1.6`: K=300 → 20 s).  The balanced-tree + integer-scaling encoding here is LINEAR (`~2 ms/leaf`).
So strict-kernel exact-certificate reflection is FEASIBLE without `native_decide`.

## The one residual to a KERNEL closure of the `ℓ=2` geom SOS identity.

`quadForm_eq_sos_of_intGram` consumes `hgram : ∀ a b, gram sqsI a b = T a b`.  Discharging it kernel-
FAST needs `gram sqsI a b` (a `List.sum` over the 1243 squares, of which only ~2.76 are nonzero per
entry) rewritten to a balanced `STree.eval` whose leaves are PROVABLY the covector products — a
covector-faithful sparse-Gram reflection (the arithmetic is proven feasible above; what remains is the
faithful-leaves + completeness bookkeeping).  This is `[RES-CERT-KERNEL-REFLECT]`, now downgraded from
"infeasible" to "feasible, wiring pending".  Connecting the resulting `T`-quadratic form to the actual
`geomForm 2 B` on bonds is the SEPARATE `[RES-GEOM-REINDEX]`. -/

namespace RatSOSEval

variable {V : ℕ} {R : Type*} [CommRing R]

/-- SOS value of a list of squares: `∑_squares coeff · (⟨cov, x⟩)²`. -/
def sosVal (sqs : List (R × (Fin V → R))) (x : Fin V → R) : R :=
  (sqs.map (fun s => s.1 * (∑ a, s.2 a * x a) ^ 2)).sum

/-- Implied Gram matrix entry: `∑_squares coeff · cov a · cov b`. -/
def gram (sqs : List (R × (Fin V → R))) (a b : Fin V) : R :=
  (sqs.map (fun s => s.1 * s.2 a * s.2 b)).sum

/-- swap `List.sum` and `Finset.sum`. -/
lemma listSum_finsetSum_comm {α ι : Type*} (l : List α) (s : Finset ι) (f : α → ι → R) :
    (l.map (fun a => ∑ i ∈ s, f a i)).sum = ∑ i ∈ s, (l.map (fun a => f a i)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [List.sum_cons, ih, Finset.sum_add_distrib]

/-- factor a constant out of a `List.sum` of right-products. -/
lemma listSum_map_mul_const {α : Type*} (l : List α) (f : α → R) (c : R) :
    (l.map (fun a => f a * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [List.sum_cons, ih, add_mul]

/-- **REUSABLE CORE.** The SOS value equals the quadratic form of the implied Gram matrix. -/
theorem sosVal_eq_gramQuad (sqs : List (R × (Fin V → R))) (x : Fin V → R) :
    sosVal sqs x = ∑ a, ∑ b, gram sqs a b * (x a * x b) := by
  unfold sosVal gram
  have hsq : ∀ s : R × (Fin V → R),
      s.1 * (∑ a, s.2 a * x a) ^ 2
        = ∑ a, ∑ b, s.1 * s.2 a * s.2 b * (x a * x b) := by
    intro s
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [List.map_congr_left (fun s _ => hsq s), listSum_finsetSum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [listSum_finsetSum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← listSum_map_mul_const]

section Ordered
variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- **REUSABLE.** Nonnegative coefficients ⇒ nonnegative SOS value. -/
theorem sosVal_nonneg
    (sqs : List (S × (Fin V → S))) (hpos : ∀ s ∈ sqs, 0 ≤ s.1) (x : Fin V → S) :
    0 ≤ sosVal sqs x := by
  unfold sosVal
  apply List.sum_nonneg
  intro y hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  exact mul_nonneg (hpos s hs) (sq_nonneg _)

end Ordered

/-- **REUSABLE.** If the implied Gram equals a target `M`, the `M`-quadratic form equals the SOS. -/
theorem gramQuad_eq_sos_of_eq
    (sqs : List (R × (Fin V → R)))
    (M : Fin V → Fin V → R) (hM : ∀ a b, gram sqs a b = M a b) (x : Fin V → R) :
    ∑ a, ∑ b, M a b * (x a * x b) = sosVal sqs x := by
  rw [sosVal_eq_gramQuad sqs x]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hM]

/-! ## ℤ → ℝ bridge: a checked integer Gram identity discharges the real one. -/

/-- cast an integer square to a real square. -/
def castSq (s : ℤ × (Fin V → ℤ)) : ℝ × (Fin V → ℝ) := ((s.1 : ℝ), fun a => (s.2 a : ℝ))

/-- **BRIDGE.** The real Gram of cast-from-ℤ data is the `Int.cast` of the integer Gram. -/
lemma gram_cast (sqsI : List (ℤ × (Fin V → ℤ))) (a b : Fin V) :
    gram (sqsI.map castSq) a b = ((gram sqsI a b : ℤ) : ℝ) := by
  unfold gram
  rw [Int.cast_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, castSq]
  push_cast
  ring

/-- **BRIDGE.** Nonnegative integer coefficients ⇒ nonnegative real SOS value of the cast data. -/
lemma sosVal_cast_nonneg (sqsI : List (ℤ × (Fin V → ℤ))) (hpos : ∀ s ∈ sqsI, 0 ≤ s.1)
    (x : Fin V → ℝ) : 0 ≤ sosVal (sqsI.map castSq) x := by
  unfold sosVal
  apply List.sum_nonneg
  intro y hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  apply mul_nonneg _ (sq_nonneg _)
  show (0:ℝ) ≤ ((t.1 : ℤ) : ℝ)
  exact_mod_cast (hpos t ht)

/-- **END-TO-END INTERFACE.** From a nonneg-coefficient integer certificate whose integer Gram
identity holds, the real quadratic form of the (integer) target `T` equals the real SOS value. -/
theorem quadForm_eq_sos_of_intGram
    (sqsI : List (ℤ × (Fin V → ℤ)))
    (T : Fin V → Fin V → ℤ) (hgram : ∀ a b, gram sqsI a b = T a b)
    (x : Fin V → ℝ) :
    ∑ a, ∑ b, ((T a b : ℤ) : ℝ) * (x a * x b) = sosVal (sqsI.map castSq) x := by
  refine gramQuad_eq_sos_of_eq (sqsI.map castSq) (fun a b => ((T a b : ℤ) : ℝ)) ?_ x
  intro a b
  rw [gram_cast, hgram]

/-- **END-TO-END INTERFACE.** …and it is nonnegative. -/
theorem quadForm_nonneg_of_intGram
    (sqsI : List (ℤ × (Fin V → ℤ)))
    (hpos : ∀ s ∈ sqsI, 0 ≤ s.1)
    (T : Fin V → Fin V → ℤ) (hgram : ∀ a b, gram sqsI a b = T a b)
    (x : Fin V → ℝ) :
    0 ≤ ∑ a, ∑ b, ((T a b : ℤ) : ℝ) * (x a * x b) := by
  rw [quadForm_eq_sos_of_intGram sqsI T hgram x]
  exact sosVal_cast_nonneg sqsI hpos x

/-! ## Reflection primitive: balanced-tree integer evaluator (linear kernel reduction). -/

/-- Balanced binary tree of integers. -/
inductive STree where
  | lf : ℤ → STree
  | nd : STree → STree → STree

/-- Evaluate by summing; a BALANCED tree reduces in the kernel with depth `O(log K)`, avoiding the
super-linear deep-left-nested spine of `List.sum`. -/
def STree.eval : STree → ℤ
  | .lf x => x
  | .nd l r => l.eval + r.eval

/-- The multiset/list of leaves, in order. -/
def STree.leaves : STree → List ℤ
  | .lf x => [x]
  | .nd l r => l.leaves ++ r.leaves

/-- **REUSABLE REFLECTION PRIMITIVE.** A balanced tree evaluates to the sum of its leaf list.  Hence
any `List.sum` may be checked via a matching balanced tree (fast kernel reduction) once the leaf list
is shown (by `rfl`) to match. -/
theorem STree.eval_eq_leaves_sum (t : STree) : t.eval = t.leaves.sum := by
  induction t with
  | lf x => simp [STree.eval, STree.leaves]
  | nd l r ihl ihr => simp [STree.eval, STree.leaves, ihl, ihr, List.sum_append]

/-! ## Covector-faithful SPARSE SOS — the reusable soundness bridge (no dense Gram materialized).

The measured obstruction of the DENSE interface `quadForm_nonneg_of_intGram` above is its hypothesis
`hgram : ∀ a b, gram sqs a b = T a b`: forming/deciding the dense `V × V` Gram is `O(V²·#squares)` and
does NOT kernel-reduce in practical time (measured `>7 min` for the `ℓ=2` Q+Slab `80×80` instance,
`compute/qslab_reflect/feas_probe.lean`).

The fix is COVECTOR-FAITHFUL: an SOS `∑ⱼ dⱼ (vⱼ · B)²` with `dⱼ ≥ 0` is nonnegative TERM-BY-TERM; the
dense Gram `∑ⱼ dⱼ vⱼ vⱼᵀ` is a *specification*, never materialized to prove positivity.  Represent each
covector `vⱼ` SPARSELY (a short list of `(coord, coeff)`), evaluate by a LINEAR fold over the nonzeros,
and read positivity off `sq_nonneg` — `List.sum_nonneg`, size-independent, no `decide`.

### What is PROVED here (no `sorry`).
* `sosQuadValue` — the sparse SOS value `∑ⱼ dⱼ (vⱼ · B)²` as a linear fold.
* `sosQuadValue_nonneg` — **THE REUSABLE SOUNDNESS BRIDGE**: `(∀ j, 0 ≤ dⱼ) → 0 ≤ sosQuadValue cert B`.
  Term-by-term, no Gram, no `decide` — the whole point.
* `scovEval_eq_denseSum`, `sosQuadValue_eq_sosVal`, `sosQuadValue_eq_gramQuad` — the BRIDGES tying the
  sparse value to the proved dense `sosVal` / `gram` core: the sparse value equals the implied dense
  Gram's quadratic form, but is *computed* as a linear fold, so the Gram is a spec and never formed. -/

/-- Evaluate a SPARSE covector `v = [(i,c),…]` at `B`: `∑_{(i,c)∈v} c · B i` — a LINEAR fold over the
listed (few) nonzeros, never a dense `Fin V`-indexed sum. -/
def scovEval (v : List (Fin V × R)) (B : Fin V → R) : R := (v.map (fun p => p.2 * B p.1)).sum

/-- The DENSE covector implied by a sparse one (coefficients accumulated per coordinate).  Used ONLY to
BRIDGE the sparse value to the proved dense `sosVal`/`gram`; the sparse machinery never evaluates it. -/
def scovDense (v : List (Fin V × R)) : Fin V → R :=
  fun a => (v.map (fun p => if p.1 = a then p.2 else 0)).sum

/-- Sparse SOS value: `∑ⱼ dⱼ · (vⱼ · B)²`.  A linear fold over the sparse data — kernel-reduces fast
(like the arithmetic `certOK`), never forming the dense Gram. -/
def sosQuadValue (cert : List (R × List (Fin V × R))) (B : Fin V → R) : R :=
  (cert.map (fun t => t.1 * (scovEval t.2 B) ^ 2)).sum

section Ordered2
variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- **THE REUSABLE SOUNDNESS BRIDGE (PROVED, no `sorry`).**  Nonnegative coefficients ⇒ the sparse SOS
value is nonnegative — proved TERM-BY-TERM via `sq_nonneg`, with the dense Gram never materialized.
Size-independent, no `decide`: this is the fix for the un-decidable dense-Gram hypothesis
`∀ a b, gram sqs a b = T a b`. -/
theorem sosQuadValue_nonneg
    (cert : List (S × List (Fin V × S))) (hpos : ∀ t ∈ cert, 0 ≤ t.1) (B : Fin V → S) :
    0 ≤ sosQuadValue cert B := by
  unfold sosQuadValue
  apply List.sum_nonneg
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  exact mul_nonneg (hpos t ht) (sq_nonneg _)

end Ordered2

/-- **BRIDGE.** The sparse covector value equals the dense inner product `∑ a, scovDense v a · B a`. -/
theorem scovEval_eq_denseSum (v : List (Fin V × R)) (B : Fin V → R) :
    scovEval v B = ∑ a, scovDense v a * B a := by
  unfold scovEval scovDense
  rw [show (∑ a, (List.map (fun p : Fin V × R => if p.1 = a then p.2 else 0) v).sum * B a)
        = ∑ a, (v.map (fun p => (if p.1 = a then p.2 else 0) * B a)).sum from ?_]
  · rw [← listSum_finsetSum_comm]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [show (∑ a, (if p.1 = a then p.2 else 0) * B a)
          = ∑ a, (if p.1 = a then p.2 * B a else 0) from ?_]
    · rw [Finset.sum_ite_eq Finset.univ p.1 (fun a => p.2 * B a)]
      simp
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      split <;> simp
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [listSum_map_mul_const]

/-- The DENSE certificate induced by a sparse one (each sparse covector accumulated into a dense one). -/
def denseCert (cert : List (R × List (Fin V × R))) : List (R × (Fin V → R)) :=
  cert.map (fun t => (t.1, scovDense t.2))

/-- **BRIDGE.** The sparse SOS value equals the proved dense `sosVal` of the induced dense cert.  So
everything proved about `sosVal`/`gram` transports to the sparse form — while the value itself is a
linear fold, never a dense-Gram computation. -/
theorem sosQuadValue_eq_sosVal (cert : List (R × List (Fin V × R))) (B : Fin V → R) :
    sosQuadValue cert B = sosVal (denseCert cert) B := by
  unfold sosQuadValue sosVal denseCert
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [scovEval_eq_denseSum]

/-- **THE REUSABLE STATEMENT (PROVED).**  The sparse SOS value IS the quadratic form of the implied
dense Gram `gram (denseCert cert)` — but it is *computed* as a linear fold, so the Gram is a
specification, never materialized.  Combined with `sosQuadValue_nonneg`, this discharges quadratic-form
positivity WITHOUT the un-decidable dense-Gram identity. -/
theorem sosQuadValue_eq_gramQuad (cert : List (R × List (Fin V × R))) (B : Fin V → R) :
    sosQuadValue cert B = ∑ a, ∑ b, gram (denseCert cert) a b * (B a * B b) := by
  rw [sosQuadValue_eq_sosVal, sosVal_eq_gramQuad]

/-! ## ℤ → ℝ bridge for the sparse form (so a real energy consumes an integer sparse certificate). -/

/-- cast a sparse integer square `(coeff, [(i,c)])` to a sparse real square. -/
def castSparse (s : ℤ × List (Fin V × ℤ)) : ℝ × List (Fin V × ℝ) :=
  ((s.1 : ℝ), s.2.map (fun p => (p.1, (p.2 : ℝ))))

/-- **BRIDGE.** `scovDense` commutes with the ℤ→ℝ cast of the covector entries. -/
lemma scovDense_castInt (v : List (Fin V × ℤ)) (a : Fin V) :
    scovDense (v.map (fun p => (p.1, ((p.2 : ℤ) : ℝ)))) a = ((scovDense v a : ℤ) : ℝ) := by
  unfold scovDense
  rw [List.map_map, Int.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  split <;> simp

/-- **BRIDGE.** `denseCert` of a cast-from-ℤ sparse cert is the cast of the integer dense cert.  So a
sparse INTEGER certificate, cast to ℝ, has the same induced dense covectors as the integer one — the
tie that lets a checked integer sparse cert discharge a real quadratic form. -/
lemma denseCert_castSparse (cert : List (ℤ × List (Fin V × ℤ))) :
    denseCert (cert.map castSparse) = (denseCert cert).map castSq := by
  unfold denseCert
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, castSparse, castSq]
  refine Prod.ext rfl ?_
  funext a
  simpa using scovDense_castInt s.2 a

end RatSOSEval
