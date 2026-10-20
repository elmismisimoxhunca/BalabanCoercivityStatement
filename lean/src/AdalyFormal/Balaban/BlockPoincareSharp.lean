import AdalyFormal.Balaban.BlockPoincare
import AdalyFormal.Balaban.BlockPoincareLemma24
import AdalyFormal.Balaban.Lemma24GeneralEll

/-!
# CMP96 `(2.123)` SHARPENED — the per-block axial-gauge Poincaré constant

**Target.** `Balaban/BlockPoincare.lean` proves CMP96 `(2.123)` with Bałaban's printed constant
`d L^d = 3·ell³`.  `Balaban/Lemma24GeneralEll.lean` shows that constant is exactly what forces the
`(2.128)` exponent down from the printed `L^{-d-1}` to `L^{-d-2}`, and names the repair:
*"a sharpening of (2.123) from `dL^d` to `O(L²)`"*.  This file settles that named residual.

## THE SOURCE, at 600 dpi (`compute/block_poincare_sharp/renders/p600-22.png`, printed p.244 —
offset established by reading the printed folio off the render itself: PDF page 22 = printed 244)

Bałaban's proof of `(2.123)`, verbatim:

> "For arbitrary `j`, `2 ≦ j ≦ d`, we have
>  `|B(x,x+e_j)|² ≦ (|x_1−y_1| + … + |x_{j−1}−y_{j−1}|) Σ |(∂_1B)(p(x'))|²`, …
>  and the plaquettes `p(x')` are parallel to `(e_{j−1},e_j), …, (e_1,e_j)`. We sum the above
>  inequalities over `x` and `j = 2,…,d`. The sum over `j` involves disjoint sets of plaquettes
>  on the right-hand side, so to get a constant in the inequality we have to consider the sum
>  over `x`. The worst situation is for `j = d` and it is easy to see that
>  `Σ_{x:⟨x,x+e_d⟩⊂B(y)} |B(x,x+e_d)|² ≦ (d−1)(L−1)²L^{d−2} Σ'_d |(∂_1B)(p)|²`,
>  hence  `Σ_{b⊂B(y)} |B(b)|² ≦ d L^d Σ_{p⊂B(y)} |(∂_1B)(p)|².`   (2.123)"

So the source's own intermediate constant is `(d−1)(L−1)²L^{d−2}` (`= 2(L−1)²L` at `d = 3`),
rounded up to `dL^d`.  **Where the factors come from, exactly** (`d = 3`; Bałaban's axial `e_1`
is this tree's direction `0`): for a direction-`e_3` bond at `x` the staircase path has TWO legs —
leg A telescopes coordinate `1` down to `y_1` through `(e_1,e_3)`-plaquettes, leg B then telescopes
coordinate `2` down to `y_2` **inside the plane `x_1 = y_1`** through `(e_2,e_3)`-plaquettes.
Cauchy–Schwarz pays the total path length `2(L−1)`.  Double counting pays the multiplicity: `L−1`
for a leg-A plaquette, but `L(L−1)` for a leg-B plaquette, because leg B is run in the single plane
`x_1 = y_1` and therefore **all `L` bonds differing only in `x_1` share it**.
`2(L−1) · L(L−1) = (d−1)(L−1)²L^{d−2}`.

**The dispatch's suspicion is refuted**: Cauchy–Schwarz pays only `2(L−1) = O(L)`, which is the
correct order.  The extra factor of `L` is the free coordinate in leg B's multiplicity.

## WHAT THIS FILE PROVES

**§1–§4 (the improvement).** Bałaban applies ONE Cauchy–Schwarz to the whole two-leg path and ONE
multiplicity to all planes, so the worse leg-B multiplicity `L(L−1)` is charged to leg A as well.
Splitting the two legs with a WEIGHTED Cauchy–Schwarz `(a+b)² ≤ (1+1/t)a² + (1+t)b²` and using
each leg's OWN multiplicity, the optimal weight is `t = 1/ell` and the constant becomes

>   `blockPoincareSharpConst ell = (ell+1)(ell−1)²`   (`= ell³ − ell² − ell + 1`)

`block_poincare_sharp` (§4) is `(2.123)` with this constant — a factor `3ell³/((ell+1)(ell−1)²) → 3`
improvement, and better than the source's own `2ell(ell−1)²` by a further `2ell/(ell+1) → 2`.

**§5 (the exact arithmetic, in ℚ).** `needed_2123_constant`: the printed `(2.128)` exponent
`ell^{-4}` (constant `1/108`) follows from Bałaban's assembly iff the `(2.123)` constant satisfies
`C ≤ (108·ell⁴ − 6·ell²)/(1 + 54·ell²)`, which is `~2ell²`.  So the improvement in §4 is NOT enough
asymptotically — and §6 proves nothing ever will be.

**§7 (the PROVED obstruction — `O(L²)` is IMPOSSIBLE).** `sw` is an explicit
admissible field on which the `(2.123)` ratio is `Θ(ell³)`.  Its mechanism is a CANCELLATION, not a
counting artifact: the direction-`1` component is tuned so that the `(1,2)`-curl vanishes on every
slice `x_0 ≠ y_0`, leaving only the single axial plane to pay — exactly the leg-B multiplicity,
realised as an identity.  Hence `dL^d`'s POWER `L^d` is sharp and the `O(L²)` repair route named in
`Lemma24GeneralEll`'s docstring is CLOSED.
~~and `Lemma24ConclusionCorrected`'s `ell^{-5}` is not an artifact of Bałaban's bookkeeping.~~
**STRUCK 2026-07-27 — CONVICTED by the blind Sol gate, and the conviction is accepted: this
theorem does not support that sentence.** What §7 closes is the `O(ell²)` route *through a uniform
per-block constant fed into this file's `bcoef` assembly*. It does **not** show `ell^{-5}` is forced,
does not prove printed `(2.128)` false, and does not exclude a different or slab-local argument —
`Lemma24GeneralEll.lean:151-154` explicitly leaves the large-`L` truth of printed `(2.128)` OPEN, and
that disclosure was already in the tree when this sentence was written. Both blind gates (Sol and
Kimi, independently and without contact) raised this same scope limit unprompted, so it is not one
reader's quibble.

**§6 (the delivered exponent).** `lemma24_sharpened`: the improved constant, pushed back through
Bałaban's own assembly, gives `ell·Σ_c|Q₁B|² + Σ_p|∂₁B|² ≥ (1/54)·ell^{-5}·‖B‖²` for every
`ell ≥ 2` — a `180/54 = 10/3` improvement on `Lemma24GeneralEll.lemma24_general_ell` at the same
exponent, pinned by `lemma24_sharpened_improves` — AND the printed `(2.128)` shape,
`(1/108)·ell^{-4}`, at `ell = 3` (`lemma24_printed_ell3`), which was previously known only at
`ell = 2`.

*Docstring corrected 2026-07-27 (blind Kimi third-gate).* This paragraph previously advertised
`(1/84)` and `180/84 = 15/7`. The theorem at line 876 delivers `1/54` and
`lemma24_sharpened_improves` pins the ratio at `10/3`, so the stale numbers UNDERSTATED the delivered
result. Recorded rather than silently overwritten because the drift ran in the conservative direction
and a future reader comparing notes to numbers deserves to know which way it pointed.

**§6a SCOPE OF `lemma24_printed_ell3` — do not call it "the printed Lemma 2.4" unqualified.**
Convicted 2026-07-27 by the blind Sol gate, and the conviction is accepted. What is proved is the
WHOLE-PERIODIC-LATTICE (torus) specialization: the statement carries no arbitrary source region `Λ`,
no `Λ = B(Λ′)` binder, no "at least one endpoint" ambient bond-set binder, and no
support-outside-`Λ` clause. CMP96's Lemma 2.4 is stated for an arbitrary `Λ`. No restriction or
extension theorem from the torus conclusion to arbitrary `Λ` exists in this tree, and this module has
no importer, so nothing currently depends on the stronger reading — but the name invites it. The
honest description is: *the printed `(2.128)` constant and exponent, on the torus, at `ell = 3`.*

## L12 / S91
`§7`'s obstruction theorems are stated `∀ K, … → lower bound ≤ K` (universally quantified over the
candidate constant), NOT `∃ B, …`: there is no existential over free data anywhere in this file, so
no `S91_REGISTRY.tsv` row is triggered.  The witness is a named `def`, not a chosen inhabitant.
-/

namespace AdalyFormal.Balaban.BlockPoincareSharp

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24

variable {L : PeriodicLatticeExtent}

/-! ## §1. The abstract WEIGHTED TWO-LEG core.

`Migration/BlockPoincare.block_poincare_core'` charges ONE `(K, M)` pair to the whole path.  This
refinement charges each leg its own `(K, M)` and pays for the split with the elementary weighted
inequality `(a+b)² ≤ (1+1/t)a² + (1+t)b²` (equality slack `(a − t·b)²/t ≥ 0`).  Nothing about
lattices, gauge groups or blocks appears. -/

section AbstractCore

variable {Bnd Plq : Type*} [Fintype Bnd] [Fintype Plq] [DecidableEq Plq]

/-- The elementary weighted two-term inequality, with its exact slack. -/
theorem weighted_add_sq (a b t : ℝ) (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + 1 / t) * a ^ 2 + (1 + t) * b ^ 2 := by
  have hslack : (0 : ℝ) ≤ (a - t * b) ^ 2 / t := by positivity
  have hkey : (1 + 1 / t) * a ^ 2 + (1 + t) * b ^ 2 - (a + b) ^ 2 = (a - t * b) ^ 2 / t := by
    field_simp; ring
  linarith [hslack, hkey]

/-- A leg's contribution: Cauchy–Schwarz on the path, then the double-counting bound, with the
multiplicity bound applied only on the leg's OWN plaquette set. -/
theorem leg_bound (stp : Bnd → Finset Plq) (S : Finset Plq) (g : Plq → ℝ) (K M : ℕ)
    (hsub : ∀ b, stp b ⊆ S) (hK : ∀ b, (stp b).card ≤ K)
    (hM : ∀ p, AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p ≤ M)
    (_hgnn : ∀ p, 0 ≤ g p) :
    ∑ b : Bnd, (∑ p ∈ stp b, g p) ^ 2 ≤ (K : ℝ) * M * ∑ p ∈ S, (g p) ^ 2 := by
  have hCS : ∀ b : Bnd, (∑ p ∈ stp b, g p) ^ 2 ≤ (K : ℝ) * ∑ p ∈ stp b, (g p) ^ 2 := by
    intro b
    have h1 : (∑ p ∈ stp b, g p) ^ 2 ≤ ((stp b).card : ℝ) * ∑ p ∈ stp b, (g p) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hc : ((stp b).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK b
    have hnn : (0 : ℝ) ≤ ∑ p ∈ stp b, (g p) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact le_trans h1 (mul_le_mul_of_nonneg_right hc hnn)
  have hdouble : (∑ b : Bnd, ∑ p ∈ stp b, (g p) ^ 2)
      = ∑ p : Plq, (AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p : ℝ) * (g p) ^ 2 :=
    AdalyFormal.Migration.BlockPoincare.sum_steps_eq_sum_mult stp (fun p => (g p) ^ 2)
  -- the multiplicity vanishes off `S`
  have hoff : ∀ p ∉ S, AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p = 0 := by
    intro p hp
    unfold AdalyFormal.Migration.BlockPoincare.plaqMultiplicity
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hmem
    exact hp (hsub b hmem)
  have hsplit : ∑ p : Plq, (AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p : ℝ)
        * (g p) ^ 2
      ≤ (M : ℝ) * ∑ p ∈ S, (g p) ^ 2 := by
    have hterm : ∀ p ∈ (Finset.univ : Finset Plq),
        (AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p : ℝ) * (g p) ^ 2
          ≤ (M : ℝ) * (if p ∈ S then (g p) ^ 2 else 0) := by
      intro p _
      by_cases hp : p ∈ S
      · rw [if_pos hp]
        have : (AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast hM p
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · rw [if_neg hp, hoff p hp]
        simp
    calc ∑ p : Plq, (AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p : ℝ) * (g p) ^ 2
        ≤ ∑ p : Plq, (M : ℝ) * (if p ∈ S then (g p) ^ 2 else 0) :=
          Finset.sum_le_sum hterm
      _ = (M : ℝ) * ∑ p : Plq, (if p ∈ S then (g p) ^ 2 else 0) := by rw [Finset.mul_sum]
      _ = (M : ℝ) * ∑ p ∈ S, (g p) ^ 2 := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  calc ∑ b : Bnd, (∑ p ∈ stp b, g p) ^ 2
      ≤ ∑ b : Bnd, (K : ℝ) * ∑ p ∈ stp b, (g p) ^ 2 := Finset.sum_le_sum (fun b _ => hCS b)
    _ = (K : ℝ) * ∑ b : Bnd, ∑ p ∈ stp b, (g p) ^ 2 := by rw [Finset.mul_sum]
    _ = (K : ℝ) * ∑ p : Plq,
          (AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stp p : ℝ) * (g p) ^ 2 := by
          rw [hdouble]
    _ ≤ (K : ℝ) * ((M : ℝ) * ∑ p ∈ S, (g p) ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = (K : ℝ) * M * ∑ p ∈ S, (g p) ^ 2 := by ring

/-- **THE WEIGHTED TWO-LEG CORE.** Each leg is charged its own path length and its own
multiplicity, over its own (necessarily disjoint) plaquette set; the split costs the weight `t`. -/
theorem two_leg_core (stpA stpB : Bnd → Finset Plq) (SA SB : Finset Plq)
    (bondAbs : Bnd → ℝ) (plaqAbs : Plq → ℝ) (KA KB MA MB : ℕ) (t : ℝ) (ht : 0 < t)
    (hsubA : ∀ b, stpA b ⊆ SA) (hsubB : ∀ b, stpB b ⊆ SB)
    (hKA : ∀ b, (stpA b).card ≤ KA) (hKB : ∀ b, (stpB b).card ≤ KB)
    (hMA : ∀ p, AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stpA p ≤ MA)
    (hMB : ∀ p, AdalyFormal.Migration.BlockPoincare.plaqMultiplicity stpB p ≤ MB)
    (hbnn : ∀ b, 0 ≤ bondAbs b) (hpnn : ∀ p, 0 ≤ plaqAbs p)
    (hTri : ∀ b, bondAbs b ≤ (∑ p ∈ stpA b, plaqAbs p) + (∑ p ∈ stpB b, plaqAbs p)) :
    ∑ b : Bnd, (bondAbs b) ^ 2
      ≤ (1 + 1 / t) * (KA : ℝ) * MA * (∑ p ∈ SA, (plaqAbs p) ^ 2)
        + (1 + t) * (KB : ℝ) * MB * (∑ p ∈ SB, (plaqAbs p) ^ 2) := by
  have hptw : ∀ b : Bnd, (bondAbs b) ^ 2
      ≤ (1 + 1 / t) * (∑ p ∈ stpA b, plaqAbs p) ^ 2
        + (1 + t) * (∑ p ∈ stpB b, plaqAbs p) ^ 2 := by
    intro b
    exact le_trans (pow_le_pow_left₀ (hbnn b) (hTri b) 2)
      (weighted_add_sq _ _ t ht)
  have hA := leg_bound stpA SA plaqAbs KA MA hsubA hKA hMA hpnn
  have hB := leg_bound stpB SB plaqAbs KB MB hsubB hKB hMB hpnn
  have hwA : (0 : ℝ) < 1 + 1 / t := by positivity
  have hwB : (0 : ℝ) < 1 + t := by positivity
  calc ∑ b : Bnd, (bondAbs b) ^ 2
      ≤ ∑ b : Bnd, ((1 + 1 / t) * (∑ p ∈ stpA b, plaqAbs p) ^ 2
            + (1 + t) * (∑ p ∈ stpB b, plaqAbs p) ^ 2) := Finset.sum_le_sum (fun b _ => hptw b)
    _ = (1 + 1 / t) * (∑ b : Bnd, (∑ p ∈ stpA b, plaqAbs p) ^ 2)
          + (1 + t) * (∑ b : Bnd, (∑ p ∈ stpB b, plaqAbs p) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (1 + 1 / t) * ((KA : ℝ) * MA * (∑ p ∈ SA, (plaqAbs p) ^ 2))
          + (1 + t) * ((KB : ℝ) * MB * (∑ p ∈ SB, (plaqAbs p) ^ 2)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hA (le_of_lt hwA))
            (mul_le_mul_of_nonneg_left hB (le_of_lt hwB))
    _ = (1 + 1 / t) * (KA : ℝ) * MA * (∑ p ∈ SA, (plaqAbs p) ^ 2)
          + (1 + t) * (KB : ℝ) * MB * (∑ p ∈ SB, (plaqAbs p) ^ 2) := by ring

#print axioms weighted_add_sq
#print axioms leg_bound
#print axioms two_leg_core

end AbstractCore

/-! ## §2. The two legs of Bałaban's staircase, split.

`BlockPoincare.steps` is the UNION of the two legs; `stepsA` is the `zK` (coordinate-`0`) leg,
whose plaquettes lie in the `(0,1)` and `(0,2)` planes, and `stepsB` is the `wK` (coordinate-`1`)
leg, whose plaquettes lie in the `(1,2)` plane.  The plane labels make them disjoint, which is
exactly the source's own observation that "the sum over `j` involves disjoint sets of plaquettes". -/

/-- The `(1,2)` plane label — leg B's plane, and the one carrying the bad multiplicity. -/
def dir12 : PeriodicPlaquetteDirections := ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩

/-- Leg A: the coordinate-`0` telescoping leg (`(0,1)`-plaquettes for a direction-`1` bond,
`(0,2)`-plaquettes for a direction-`2` bond). -/
def stepsA (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    Finset (PeriodicLatticePlaquette L) :=
  if bondInBlock y ell b then
    if b.2 = 1 then
      (Finset.range ((b.1 0).val - (y 0).val)).image
        (fun k => (zK y b.1 k, (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))
    else if b.2 = 2 then
      (Finset.range ((b.1 0).val - (y 0).val)).image
        (fun k => (zK y b.1 k, (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))
    else ∅
  else ∅

/-- Leg B: the coordinate-`1` telescoping leg, run inside the plane `x_0 = y_0`; `(1,2)`-plaquettes,
and only direction-`2` bonds have one. -/
def stepsB (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    Finset (PeriodicLatticePlaquette L) :=
  if bondInBlock y ell b then
    if b.2 = 1 then ∅
    else if b.2 = 2 then
      (Finset.range ((b.1 1).val - (y 1).val)).image (fun k => (wK y b.1 k, dir12))
    else ∅
  else ∅

theorem steps_eq_union (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    steps y ell b = stepsA y ell b ∪ stepsB y ell b := by
  unfold steps stepsA stepsB dir12
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb, if_pos hbb, if_pos hbb]
    by_cases h1 : b.2 = 1
    · rw [if_pos h1, if_pos h1, if_pos h1]; simp
    · rw [if_neg h1, if_neg h1, if_neg h1]
      by_cases h2 : b.2 = 2
      · rw [if_pos h2, if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, if_neg h2]; simp
  · rw [if_neg hbb, if_neg hbb, if_neg hbb]; simp

/-- Leg A's plaquettes never carry the `(1,2)` label. -/
theorem stepsA_ne_dir12 {y : PeriodicLatticeSite L} {ell : ℕ} {b : Bond L}
    {p : PeriodicLatticePlaquette L} (hp : p ∈ stepsA y ell b) : p.2 ≠ dir12 := by
  unfold stepsA at hp
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb] at hp
    by_cases h1 : b.2 = 1
    · rw [if_pos h1, Finset.mem_image] at hp
      obtain ⟨k, _, hpk⟩ := hp
      subst hpk
      have hne : (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections) ≠ dir12 := by
        unfold dir12; decide
      exact hne
    · rw [if_neg h1] at hp
      by_cases h2 : b.2 = 2
      · rw [if_pos h2, Finset.mem_image] at hp
        obtain ⟨k, _, hpk⟩ := hp
        subst hpk
        have hne : (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections) ≠ dir12 := by
          unfold dir12; decide
        exact hne
      · rw [if_neg h2] at hp; exact absurd hp (Finset.notMem_empty p)
  · rw [if_neg hbb] at hp; exact absurd hp (Finset.notMem_empty p)

/-- Leg B's plaquettes always carry the `(1,2)` label. -/
theorem stepsB_eq_dir12 {y : PeriodicLatticeSite L} {ell : ℕ} {b : Bond L}
    {p : PeriodicLatticePlaquette L} (hp : p ∈ stepsB y ell b) : p.2 = dir12 := by
  unfold stepsB at hp
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb] at hp
    by_cases h1 : b.2 = 1
    · rw [if_pos h1] at hp; exact absurd hp (Finset.notMem_empty p)
    · rw [if_neg h1] at hp
      by_cases h2 : b.2 = 2
      · rw [if_pos h2, Finset.mem_image] at hp
        obtain ⟨k, _, hpk⟩ := hp
        subst hpk; rfl
      · rw [if_neg h2] at hp; exact absurd hp (Finset.notMem_empty p)
  · rw [if_neg hbb] at hp; exact absurd hp (Finset.notMem_empty p)

theorem stepsA_disjoint_stepsB (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    Disjoint (stepsA y ell b) (stepsB y ell b) := by
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact stepsA_ne_dir12 hpA (stepsB_eq_dir12 hpB)

/-- The leg-split triangle inequality, INHERITED from `BlockPoincare.steps_hTri` — no geometry is
re-derived: `steps = stepsA ⊔ stepsB` disjointly, so the single sum splits. -/
theorem steps_hTri_split {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) (b : Bond L) :
    bAbs B y ell b ≤ (∑ p ∈ stepsA y ell b, pAbs B y ell p)
      + (∑ p ∈ stepsB y ell b, pAbs B y ell p) := by
  have h := steps_hTri hstrict0 hstrict1 hstrict2 B hB y hy b
  rw [steps_eq_union y ell b, Finset.sum_union (stepsA_disjoint_stepsB y ell b)] at h
  exact h

/-! ## §3. Each leg's own path length and multiplicity.

Leg A: length `≤ ell−1`, multiplicity `≤ ell−1` — one free coordinate (`x_0`), and its offset is
`≥ 1`.  Leg B: length `≤ ell−1`, multiplicity `≤ ell·(ell−1)` — TWO free coordinates, because `wK`
forgets `x_0` entirely.  That asymmetry is the whole content of the sharpening. -/

theorem stepsA_hK (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    (stepsA y ell b).card ≤ ell - 1 := by
  unfold stepsA
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb]
    obtain ⟨hx, _⟩ := hbb
    have h0ge := (mem_blockOf.mp hx) 0 |>.1
    have h0lt := (mem_blockOf.mp hx) 0 |>.2
    by_cases h1 : b.2 = 1
    · rw [if_pos h1]
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_range]; omega
    · rw [if_neg h1]
      by_cases h2 : b.2 = 2
      · rw [if_pos h2]
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_range]; omega
      · rw [if_neg h2]; simp
  · rw [if_neg hbb]; simp

theorem stepsB_hK (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    (stepsB y ell b).card ≤ ell - 1 := by
  unfold stepsB
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb]
    obtain ⟨hx, _⟩ := hbb
    have h1ge := (mem_blockOf.mp hx) 1 |>.1
    have h1lt := (mem_blockOf.mp hx) 1 |>.2
    by_cases h1 : b.2 = 1
    · rw [if_pos h1]; simp
    · rw [if_neg h1]
      by_cases h2 : b.2 = 2
      · rw [if_pos h2]
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_range]; omega
      · rw [if_neg h2]; simp
  · rw [if_neg hbb]; simp

/-- **Leg-A read-off.** From `p ∈ stepsA y ell b` one recovers the bond's coordinates `1` and `2`
and its direction from `p` ALONE (the `zK` walk moves only coordinate `0`), and the coordinate-`0`
offset is `≥ 1`.  Hence only `ell−1` bonds can share a leg-A plaquette. -/
theorem stepsA_recover {ell : ℕ} {y : PeriodicLatticeSite L} {b : Bond L}
    {p : PeriodicLatticePlaquette L} (hp : p ∈ stepsA y ell b) :
    b.1 1 = p.1 1 ∧ b.1 2 = p.1 2 ∧ 1 ≤ (b.1 0).val - (y 0).val ∧
      b.2 = (if p.2 = (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)
        then (1 : Fin 3) else 2) := by
  unfold stepsA at hp
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb] at hp
    by_cases h1 : b.2 = 1
    · rw [if_pos h1, Finset.mem_image] at hp
      obtain ⟨k, hk, hpk⟩ := hp
      rw [Finset.mem_range] at hk
      subst hpk
      refine ⟨?_, ?_, by omega, ?_⟩
      · show b.1 1 = (zK y b.1 k) 1
        rw [zK_coord_ne y b.1 k (by decide : (1:Fin 3) ≠ 0)]
      · show b.1 2 = (zK y b.1 k) 2
        rw [zK_coord_ne y b.1 k (by decide : (2:Fin 3) ≠ 0)]
      · rw [if_pos rfl]; exact h1
    · rw [if_neg h1] at hp
      by_cases h2 : b.2 = 2
      · rw [if_pos h2, Finset.mem_image] at hp
        obtain ⟨k, hk, hpk⟩ := hp
        rw [Finset.mem_range] at hk
        subst hpk
        refine ⟨?_, ?_, by omega, ?_⟩
        · show b.1 1 = (zK y b.1 k) 1
          rw [zK_coord_ne y b.1 k (by decide : (1:Fin 3) ≠ 0)]
        · show b.1 2 = (zK y b.1 k) 2
          rw [zK_coord_ne y b.1 k (by decide : (2:Fin 3) ≠ 0)]
        · have hne : (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)
              ≠ ⟨((0:Fin 3),(1:Fin 3)), by decide⟩ := by decide
          rw [if_neg hne]; exact h2
      · rw [if_neg h2] at hp; exact absurd hp (Finset.notMem_empty p)
  · rw [if_neg hbb] at hp; exact absurd hp (Finset.notMem_empty p)

/-- **Leg-B read-off.** From `p ∈ stepsB y ell b` one recovers coordinate `2` and the direction
(`= 2`), and the coordinate-`1` offset is `≥ 1`.  Coordinates `0` AND `1` are NOT recoverable —
`wK y x k` sets coordinate `0` to `y_0` and coordinate `1` to `y_1 + k`, forgetting both of `x`'s.
That is the free-coordinate loss, exactly. -/
theorem stepsB_recover {ell : ℕ} {y : PeriodicLatticeSite L} {b : Bond L}
    {p : PeriodicLatticePlaquette L} (hp : p ∈ stepsB y ell b) :
    b.1 2 = p.1 2 ∧ 1 ≤ (b.1 1).val - (y 1).val ∧ b.2 = 2 := by
  unfold stepsB at hp
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb] at hp
    by_cases h1 : b.2 = 1
    · rw [if_pos h1] at hp; exact absurd hp (Finset.notMem_empty p)
    · rw [if_neg h1] at hp
      by_cases h2 : b.2 = 2
      · rw [if_pos h2, Finset.mem_image] at hp
        obtain ⟨k, hk, hpk⟩ := hp
        rw [Finset.mem_range] at hk
        subst hpk
        refine ⟨?_, by omega, h2⟩
        show b.1 2 = (wK y b.1 k) 2
        rw [wK_coord2 y b.1 k]
      · rw [if_neg h2] at hp; exact absurd hp (Finset.notMem_empty p)
  · rw [if_neg hbb] at hp; exact absurd hp (Finset.notMem_empty p)

theorem stepsA_bondInBlock {ell : ℕ} {y : PeriodicLatticeSite L} {b : Bond L}
    {p : PeriodicLatticePlaquette L} (hp : p ∈ stepsA y ell b) : bondInBlock y ell b := by
  by_contra hc
  unfold stepsA at hp
  rw [if_neg hc] at hp
  exact absurd hp (Finset.notMem_empty p)

theorem stepsB_bondInBlock {ell : ℕ} {y : PeriodicLatticeSite L} {b : Bond L}
    {p : PeriodicLatticePlaquette L} (hp : p ∈ stepsB y ell b) : bondInBlock y ell b := by
  by_contra hc
  unfold stepsB at hp
  rw [if_neg hc] at hp
  exact absurd hp (Finset.notMem_empty p)

/-- **Leg-A multiplicity `≤ ell−1`** — the refinement.  `BlockPoincare.steps_hM` can only give
`ell²` because it must cover leg B; leg A alone has a single free coordinate. -/
theorem stepsA_hM {ell : ℕ} (y : PeriodicLatticeSite L) (p : PeriodicLatticePlaquette L) :
    AdalyFormal.Migration.BlockPoincare.plaqMultiplicity (stepsA y ell) p ≤ ell - 1 := by
  unfold AdalyFormal.Migration.BlockPoincare.plaqMultiplicity
  have hcard : (Finset.range (ell - 1)).card = ell - 1 := Finset.card_range _
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun b : Bond L => (b.1 0).val - (y 0).val - 1)
  · intro b hb
    have hp : p ∈ stepsA y ell b := (Finset.mem_filter.mp hb).2
    obtain ⟨hx, _⟩ := stepsA_bondInBlock hp
    obtain ⟨_, _, hge1, _⟩ := stepsA_recover hp
    have h0ge := (mem_blockOf.mp hx) 0 |>.1
    have h0lt := (mem_blockOf.mp hx) 0 |>.2
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  · intro b hb b' hb' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
    have hp := hb.2
    have hp' := hb'.2
    obtain ⟨hx, _⟩ := stepsA_bondInBlock hp
    obtain ⟨hx', _⟩ := stepsA_bondInBlock hp'
    obtain ⟨h1, h2, hge1, hdir⟩ := stepsA_recover hp
    obtain ⟨h1', h2', hge1', hdir'⟩ := stepsA_recover hp'
    have hb0ge := (mem_blockOf.mp hx) 0 |>.1
    have hb0ge' := (mem_blockOf.mp hx') 0 |>.1
    have heq' : (b.1 0).val - (y 0).val - 1 = (b'.1 0).val - (y 0).val - 1 := heq
    have hval0 : (b.1 0).val = (b'.1 0).val := by omega
    have hsite : b.1 = b'.1 := by
      funext μ
      by_cases hμ0 : μ = 0
      · subst hμ0; exact Fin.ext hval0
      · by_cases hμ1 : μ = 1
        · subst hμ1; exact h1.trans h1'.symm
        · have hμ2 : μ = 2 := by
            have := μ.isLt
            have ha : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
            have hbb : μ.val ≠ 1 := fun h => hμ1 (Fin.ext h)
            apply Fin.ext; omega
          subst hμ2; exact h2.trans h2'.symm
    exact Prod.ext hsite (hdir.trans hdir'.symm)

/-- **Leg-B multiplicity `≤ ell·(ell−1)`** — the source's own `L(L−1)`, and the reason `(2.123)`
carries `L^d` rather than `L²`. -/
theorem stepsB_hM {ell : ℕ} (y : PeriodicLatticeSite L) (p : PeriodicLatticePlaquette L) :
    AdalyFormal.Migration.BlockPoincare.plaqMultiplicity (stepsB y ell) p ≤ ell * (ell - 1) := by
  unfold AdalyFormal.Migration.BlockPoincare.plaqMultiplicity
  have hcard : (Finset.range ell ×ˢ Finset.range (ell - 1)).card = ell * (ell - 1) := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun b : Bond L => ((b.1 0).val - (y 0).val, (b.1 1).val - (y 1).val - 1))
  · intro b hb
    have hp : p ∈ stepsB y ell b := (Finset.mem_filter.mp hb).2
    obtain ⟨hx, _⟩ := stepsB_bondInBlock hp
    obtain ⟨_, hge1, _⟩ := stepsB_recover hp
    have h0ge := (mem_blockOf.mp hx) 0 |>.1
    have h0lt := (mem_blockOf.mp hx) 0 |>.2
    have h1ge := (mem_blockOf.mp hx) 1 |>.1
    have h1lt := (mem_blockOf.mp hx) 1 |>.2
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · intro b hb b' hb' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
    have hp := hb.2
    have hp' := hb'.2
    obtain ⟨hx, _⟩ := stepsB_bondInBlock hp
    obtain ⟨hx', _⟩ := stepsB_bondInBlock hp'
    obtain ⟨h2, hge1, hdir⟩ := stepsB_recover hp
    obtain ⟨h2', hge1', hdir'⟩ := stepsB_recover hp'
    have heqp : ((b.1 0).val - (y 0).val, (b.1 1).val - (y 1).val - 1)
        = ((b'.1 0).val - (y 0).val, (b'.1 1).val - (y 1).val - 1) := heq
    have he0 : (b.1 0).val - (y 0).val = (b'.1 0).val - (y 0).val := congrArg Prod.fst heqp
    have he1 : (b.1 1).val - (y 1).val - 1 = (b'.1 1).val - (y 1).val - 1 :=
      congrArg Prod.snd heqp
    have hb0ge := (mem_blockOf.mp hx) 0 |>.1
    have hb1ge := (mem_blockOf.mp hx) 1 |>.1
    have hb0ge' := (mem_blockOf.mp hx') 0 |>.1
    have hb1ge' := (mem_blockOf.mp hx') 1 |>.1
    have hval0 : (b.1 0).val = (b'.1 0).val := by omega
    have hval1 : (b.1 1).val = (b'.1 1).val := by omega
    have hsite : b.1 = b'.1 := by
      funext μ
      by_cases hμ0 : μ = 0
      · subst hμ0; exact Fin.ext hval0
      · by_cases hμ1 : μ = 1
        · subst hμ1; exact Fin.ext hval1
        · have hμ2 : μ = 2 := by
            have := μ.isLt
            have ha : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
            have hbb : μ.val ≠ 1 := fun h => hμ1 (Fin.ext h)
            apply Fin.ext; omega
          subst hμ2; exact h2.trans h2'.symm
    exact Prod.ext hsite (hdir.trans hdir'.symm)

/-! ## §4. THE SHARPENED `(2.123)`. -/

/-- The two legs' plaquette sets: leg A's plaquettes carry a plane label `≠ (1,2)`. -/
def plaqsA (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticePlaquette L) :=
  (plaqsInBlock y ell).filter (fun p => p.2 ≠ dir12)

def plaqsB (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticePlaquette L) :=
  (plaqsInBlock y ell).filter (fun p => p.2 = dir12)

theorem plaqsAB_disjoint (y : PeriodicLatticeSite L) (ell : ℕ) :
    Disjoint (plaqsA y ell) (plaqsB y ell) := by
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact (Finset.mem_filter.mp hpA).2 (Finset.mem_filter.mp hpB).2

theorem plaqsAB_union (y : PeriodicLatticeSite L) (ell : ℕ) :
    plaqsA y ell ∪ plaqsB y ell = plaqsInBlock y ell := by
  unfold plaqsA plaqsB
  rw [← Finset.filter_or]
  apply Finset.filter_true_of_mem
  intro p _
  by_cases h : p.2 = dir12
  · exact Or.inr h
  · exact Or.inl h

theorem stepsA_sub {ell : ℕ} (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (y : PeriodicLatticeSite L) (b : Bond L) : stepsA y ell b ⊆ plaqsA y ell := by
  intro p hp
  refine Finset.mem_filter.mpr ⟨?_, stepsA_ne_dir12 hp⟩
  obtain ⟨hx, hshiftb⟩ := stepsA_bondInBlock hp
  rw [mem_plaqsInBlock]
  unfold stepsA at hp
  rw [if_pos ⟨hx, hshiftb⟩] at hp
  by_cases h1 : b.2 = 1
  · rw [if_pos h1, Finset.mem_image] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    rw [Finset.mem_range] at hk
    subst hpk
    have hshift1 : periodicLatticeShift b.1 1 ∈ blockOf y ell := by rw [← h1]; exact hshiftb
    exact plaq01_mem hstrict1 y b.1 hx hshift1 (by omega)
  · rw [if_neg h1] at hp
    by_cases h2 : b.2 = 2
    · rw [if_pos h2, Finset.mem_image] at hp
      obtain ⟨k, hk, hpk⟩ := hp
      rw [Finset.mem_range] at hk
      subst hpk
      have hshift2 : periodicLatticeShift b.1 2 ∈ blockOf y ell := by rw [← h2]; exact hshiftb
      exact plaq02_mem hstrict2 y b.1 hx hshift2 (by omega)
    · rw [if_neg h2] at hp; exact absurd hp (Finset.notMem_empty p)

theorem stepsB_sub {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y : PeriodicLatticeSite L) (b : Bond L) : stepsB y ell b ⊆ plaqsB y ell := by
  intro p hp
  refine Finset.mem_filter.mpr ⟨?_, stepsB_eq_dir12 hp⟩
  obtain ⟨hx, hshiftb⟩ := stepsB_bondInBlock hp
  rw [mem_plaqsInBlock]
  unfold stepsB at hp
  rw [if_pos ⟨hx, hshiftb⟩] at hp
  by_cases h1 : b.2 = 1
  · rw [if_pos h1] at hp; exact absurd hp (Finset.notMem_empty p)
  · rw [if_neg h1] at hp
    by_cases h2 : b.2 = 2
    · rw [if_pos h2, Finset.mem_image] at hp
      obtain ⟨k, hk, hpk⟩ := hp
      rw [Finset.mem_range] at hk
      subst hpk
      have hshift2 : periodicLatticeShift b.1 2 ∈ blockOf y ell := by rw [← h2]; exact hshiftb
      exact plaq12_mem hstrict2 y b.1 hx hshift2 (by omega)
    · rw [if_neg h2] at hp; exact absurd hp (Finset.notMem_empty p)

/-- **The sharpened `(2.123)` constant.** `(ell+1)(ell−1)² = ell³ − ell² − ell + 1`, versus
Bałaban's printed `dL^d = 3ell³` and his own intermediate `2ell(ell−1)²`. -/
noncomputable def blockPoincareSharpConst (ell : ℕ) : ℝ :=
  ((ell : ℝ) + 1) * ((ell : ℝ) - 1) ^ 2

theorem blockPoincareSharpConst_lt (ell : ℕ) (hell : 2 ≤ ell) :
    blockPoincareSharpConst ell < 3 * (ell : ℝ) ^ 3 := by
  have h2 : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  unfold blockPoincareSharpConst
  nlinarith [h2, sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) - 2)]

/-- **CMP96 `(2.123)`, SHARPENED.**  `Σ_{b⊂B(y)}|B(b)|² ≤ (ell+1)(ell−1)²·Σ_{p⊂B(y)}|(∂₁B)(p)|²`,
a factor `→ 3` better than the printed `dL^d`, obtained by charging each leg of Bałaban's staircase
its OWN multiplicity through the weighted Cauchy–Schwarz at the optimal weight `t = 1/ell`.
Hypotheses are exactly `BlockPoincare.block_poincare`'s, plus `2 ≤ ell`. -/
theorem block_poincare_sharp {ell : ℕ} (hell : 2 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) :
    ∑ b ∈ bondsInBlock y ell, (B b) ^ 2
      ≤ blockPoincareSharpConst ell * ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have ht : (0 : ℝ) < 1 / (ell : ℝ) := by positivity
  have hcore := two_leg_core (stepsA y ell) (stepsB y ell) (plaqsA y ell) (plaqsB y ell)
    (bAbs B y ell) (pAbs B y ell) (ell - 1) (ell - 1) (ell - 1) (ell * (ell - 1))
    (1 / (ell : ℝ)) ht
    (stepsA_sub hstrict1 hstrict2 y) (stepsB_sub hstrict2 y)
    (stepsA_hK y ell) (stepsB_hK y ell) (stepsA_hM y) (stepsB_hM y)
    (fun b => by unfold bAbs; split <;> [exact abs_nonneg _; exact le_refl 0])
    (fun p => by unfold pAbs; split <;> [exact abs_nonneg _; exact le_refl 0])
    (steps_hTri_split hstrict0 hstrict1 hstrict2 B hB y hy)
  -- cast the ℕ constants
  have hcast1 : (((ell - 1 : ℕ)) : ℝ) = (ell : ℝ) - 1 := by
    have : (1 : ℕ) ≤ ell := by omega
    push_cast [Nat.cast_sub this]; ring
  have hcast2 : (((ell * (ell - 1) : ℕ)) : ℝ) = (ell : ℝ) * ((ell : ℝ) - 1) := by
    have h1 : (1 : ℕ) ≤ ell := by omega
    push_cast [Nat.cast_sub h1]; ring
  rw [hcast1, hcast2] at hcore
  -- both weighted coefficients equal the sharp constant
  have hellne : (ell : ℝ) ≠ 0 := by positivity
  have hcA : (1 + 1 / (1 / (ell : ℝ))) * ((ell : ℝ) - 1) * ((ell : ℝ) - 1)
      = blockPoincareSharpConst ell := by
    unfold blockPoincareSharpConst
    rw [one_div_one_div]
    ring
  have hcB : (1 + 1 / (ell : ℝ)) * ((ell : ℝ) - 1) * ((ell : ℝ) * ((ell : ℝ) - 1))
      = blockPoincareSharpConst ell := by
    unfold blockPoincareSharpConst
    field_simp
  rw [hcA, hcB] at hcore
  rw [bondAbs_sq_sum] at hcore
  -- reassemble the two plaquette sums into the block sum
  have hAB : (∑ p ∈ plaqsA y ell, (pAbs B y ell p) ^ 2)
      + (∑ p ∈ plaqsB y ell, (pAbs B y ell p) ^ 2)
      = ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 := by
    rw [← Finset.sum_union (plaqsAB_disjoint y ell), plaqsAB_union y ell]
    apply Finset.sum_congr rfl
    intro p hp
    unfold pAbs
    rw [if_pos (mem_plaqsInBlock.mp hp), sq_abs]
  calc ∑ b ∈ bondsInBlock y ell, (B b) ^ 2
      ≤ blockPoincareSharpConst ell * (∑ p ∈ plaqsA y ell, (pAbs B y ell p) ^ 2)
        + blockPoincareSharpConst ell * (∑ p ∈ plaqsB y ell, (pAbs B y ell p) ^ 2) := hcore
    _ = blockPoincareSharpConst ell * ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 := by
        rw [← mul_add, hAB]

#print axioms dir12
#print axioms steps_eq_union
#print axioms steps_hTri_split
#print axioms stepsA_hM
#print axioms stepsB_hM
#print axioms block_poincare_sharp
#print axioms blockPoincareSharpConst_lt

/-- The sharpened `(2.123)`, summed over the coarse lattice — the drop-in replacement for
`BlockPoincareLemma24.region_2123`. -/
theorem region_2123_sharp {ell : ℕ} (hell : 2 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    inBlockBondEnergy ell B ≤ blockPoincareSharpConst ell * inBlockCurlEnergy ell B := by
  unfold inBlockBondEnergy inBlockCurlEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  exact block_poincare_sharp hell hstrict0 hstrict1 hstrict2 B hB y hy

#print axioms region_2123_sharp

/-! ## §5. THE EXACT ARITHMETIC — what the printed `(2.128)` exponent demands of `(2.123)`.

Bałaban's `(2.128)` assembly, as compiled in `Lemma24GeneralEll.lemma24_general_ell`, reduces to
one size bound (read off that proof: `hbig` + `hF1` + `hR2` + `hF2`):

>   `‖B‖² ≤ 3·ell⁵·Qtot + [6·ell² + (54·ell² + 1)·C(ell)]·Ptot`

with `C(ell)` the `(2.123)` constant.  Its conclusion `ell·Qtot + Ptot ≥ γ·‖B‖²` therefore holds
as soon as `γ·3ell⁵ ≤ ell` and `γ·Bcoef ≤ 1`.  Everything below is exact rational arithmetic on
that pair of conditions; nothing is estimated. -/

/-- The `Ptot` coefficient of Bałaban's assembly as a function of the `(2.123)` constant. -/
noncomputable def bcoef (ell : ℕ) (C : ℝ) : ℝ := 6 * (ell : ℝ) ^ 2 + (54 * (ell : ℝ) ^ 2 + 1) * C

/-- **The exact requirement on the `(2.123)` constant for the PRINTED exponent `ell^{-4}`.**
`Bcoef ≤ 108·ell⁴` — the `1/108` of `Lemma24Conclusion` — holds iff
`C ≤ (108·ell⁴ − 6·ell²)/(54·ell² + 1)`. -/
theorem needed_2123_constant (ell : ℕ) (C : ℝ) (hell : 1 ≤ ell) :
    bcoef ell C ≤ 108 * (ell : ℝ) ^ 4
      ↔ C ≤ (108 * (ell : ℝ) ^ 4 - 6 * (ell : ℝ) ^ 2) / (54 * (ell : ℝ) ^ 2 + 1) := by
  have hR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hden : (0 : ℝ) < 54 * (ell : ℝ) ^ 2 + 1 := by positivity
  unfold bcoef
  rw [le_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith [h]

/-- **The requirement is asymptotically `2·ell²`, from below.**  `(108ell⁴ − 6ell²)/(54ell²+1)
< 2ell²` for every `ell`, so ANY `(2.123)` constant reaching the printed exponent at every `ell`
would have to be `O(ell²)` — indeed `< 2ell²`. -/
theorem needed_2123_constant_lt_two_sq (ell : ℕ) (hell : 1 ≤ ell) :
    (108 * (ell : ℝ) ^ 4 - 6 * (ell : ℝ) ^ 2) / (54 * (ell : ℝ) ^ 2 + 1) < 2 * (ell : ℝ) ^ 2 := by
  have hR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hden : (0 : ℝ) < 54 * (ell : ℝ) ^ 2 + 1 := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [hR, sq_nonneg ((ell : ℝ) - 1), pow_pos (lt_of_lt_of_le zero_lt_one hR) 2]

/-- **Bałaban's printed `dL^d = 3ell³` violates the requirement at every `ell ≥ 1`** — the exact
statement of the gap `Lemma24GeneralEll` discovered, now as a standalone kernel fact. -/
theorem printed_const_fails_requirement (ell : ℕ) (hell : 1 ≤ ell) :
    108 * (ell : ℝ) ^ 4 < bcoef ell (3 * (ell : ℝ) ^ 3) := by
  have hR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  unfold bcoef
  nlinarith [hR, pow_pos (lt_of_lt_of_le zero_lt_one hR) 2,
    pow_pos (lt_of_lt_of_le zero_lt_one hR) 4, pow_pos (lt_of_lt_of_le zero_lt_one hR) 5]

/-- **The sharpened constant MEETS the requirement at `ell = 2` and `ell = 3`** — exact rationals:
`Bcoef(2) = 675 ≤ 1728` and `Bcoef(3) = 7846 ≤ 8748`. -/
theorem sharp_const_meets_requirement_ell2 :
    bcoef 2 (blockPoincareSharpConst 2) = 675 ∧ (675 : ℝ) ≤ 108 * (2 : ℝ) ^ 4 := by
  refine ⟨?_, by norm_num⟩
  unfold bcoef blockPoincareSharpConst
  norm_num

theorem sharp_const_meets_requirement_ell3 :
    bcoef 3 (blockPoincareSharpConst 3) = 7846 ∧ (7846 : ℝ) ≤ 108 * (3 : ℝ) ^ 4 := by
  refine ⟨?_, by norm_num⟩
  unfold bcoef blockPoincareSharpConst
  norm_num

/-- **…and FAILS it from `ell = 4` on** — exact rationals: `Bcoef(4) = 39021 > 27648`. -/
theorem sharp_const_fails_requirement_ell4 :
    bcoef 4 (blockPoincareSharpConst 4) = 39021 ∧ 108 * (4 : ℝ) ^ 4 < 39021 := by
  refine ⟨?_, by norm_num⟩
  unfold bcoef blockPoincareSharpConst
  norm_num

/-- **The `ell^{-5}` constant the sharpened `(2.123)` delivers: `Bcoef ≤ 54·ell⁵` for every
`ell ≥ 2`**, versus the `180·ell⁵` the printed `3ell³` forces in `lemma24_general_ell`.
Exact expansion: `Bcoef = 54ell⁵ − 54ell⁴ − 53ell³ + 59ell² − ell + 1`. -/
theorem sharp_bcoef_expand (ell : ℕ) :
    bcoef ell (blockPoincareSharpConst ell)
      = 54 * (ell : ℝ) ^ 5 - 54 * (ell : ℝ) ^ 4 - 53 * (ell : ℝ) ^ 3
        + 59 * (ell : ℝ) ^ 2 - (ell : ℝ) + 1 := by
  unfold bcoef blockPoincareSharpConst; ring

theorem sharp_bcoef_le (ell : ℕ) (hell : 2 ≤ ell) :
    bcoef ell (blockPoincareSharpConst ell) ≤ 54 * (ell : ℝ) ^ 5 := by
  have hR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  rw [sharp_bcoef_expand]
  nlinarith [hR, sq_nonneg ((ell : ℝ) - 2), pow_pos (lt_of_lt_of_le zero_lt_two hR) 2,
    pow_pos (lt_of_lt_of_le zero_lt_two hR) 3, pow_pos (lt_of_lt_of_le zero_lt_two hR) 4,
    mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg ((ell : ℝ) - 2))]

#print axioms needed_2123_constant
#print axioms needed_2123_constant_lt_two_sq
#print axioms printed_const_fails_requirement
#print axioms sharp_const_meets_requirement_ell2
#print axioms sharp_const_meets_requirement_ell3
#print axioms sharp_const_fails_requirement_ell4
#print axioms sharp_bcoef_expand
#print axioms sharp_bcoef_le

/-! ## §6. THE DELIVERED EXPONENT — the sharpened `(2.123)` pushed back through Bałaban's own
`(2.128)` assembly.

Nothing of the assembly is re-derived: `perC_bond` and the four banked geometric facts are taken
verbatim from `Lemma24GeneralEll`, and only the `(2.123)` input is replaced.  The `Sin ≤ C·Ptot`
step is `region_2123_sharp` instead of `region_2123`. -/

section Assembly

open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly
open AdalyFormal.Balaban.Lemma24GeneralEll
open GeomScratch

variable {ell : ℕ}

/-- **The size bound of Bałaban's assembly with the SHARPENED `(2.123)` input.**
`‖B‖² ≤ 3ell⁵·Qtot + Bcoef·Ptot` with `Bcoef = 6ell² + (54ell²+1)(ell+1)(ell−1)²`.  Every other
ingredient is `Lemma24GeneralEll`'s, unchanged. -/
theorem sharp_size_bound (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    bondNormSq B ≤ 3 * (ell : ℝ) ^ 5 * coarseQEnergy ell B
      + bcoef ell (blockPoincareSharpConst ell) * totalCurlEnergy B := by
  have hell : 0 < ell := by omega
  set t : ℝ := (ell : ℝ) with hT
  have ht0 : (0 : ℝ) < t := by rw [hT]; exact_mod_cast hell
  set N := bondNormSq B with hN
  set Sin := inBlockBondEnergy ell B with hSin
  set Ptot := totalCurlEnergy B with hPtot
  set Qtot := coarseQEnergy ell B with hQtot
  have hPnn : (0 : ℝ) ≤ Ptot := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSinnn : (0 : ℝ) ≤ Sin :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hsum := Finset.sum_le_sum
    (fun c (_ : c ∈ (Finset.univ : Finset (CoarseBond L ell))) => perC_bond hell hdvd B c)
  have hLHS : ∑ c : CoarseBond L ell, (1 / 3) * (1 / t ^ 4) * topFaceEnergy B c.1.1 ell c.2
      = (1 / 3) * (1 / t ^ 4) * ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2 := by
    rw [← Finset.mul_sum]
  have hRHS : ∑ c : CoarseBond L ell,
        ((t * (lineCoarseRestrict ell B c) ^ 2
          + (1 / t ^ 2) * regionCurlEnergy B c.1.1 ell c.2)
          + 3 * (1 / t ^ 2) * boundaryCorr B c.1.1 ell c.2)
      = t * Qtot + (1 / t ^ 2) * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + 3 * (1 / t ^ 2) * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hQtot, coarseQEnergy]
  rw [hLHS, hRHS] at hsum
  have hF1 := sum_topFace_ge_Sbet (L := L) (ell := ell) hell hdvd hstrict B
  have hF2 := sum_boundaryCorr_le (L := L) (ell := ell) hdvd B
  rw [← hN, ← hSin] at hF1
  rw [← hSin] at hF2
  have hF4 := sum_regionCurl_le_slabCurl (L := L) (ell := ell) B
  have hslab := slabCurlEnergy_eq_two_totalCurl (L := L) (ell := ell) hell hdvd B
  -- THE ONLY CHANGED INPUT: the sharpened (2.123)
  have h2123 := region_2123_sharp (L := L) (ell := ell) hell2
    (hstrict 0) (hstrict 1) (hstrict 2) B hB
  have hPin := inBlockCurl_le_total (L := L) (ell := ell) B
  have hCnn : (0 : ℝ) ≤ blockPoincareSharpConst ell := by
    unfold blockPoincareSharpConst
    have : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
    positivity
  have hSinC : Sin ≤ blockPoincareSharpConst ell * Ptot := by
    rw [hSin, hPtot]
    exact le_trans h2123 (mul_le_mul_of_nonneg_left hPin hCnn)
  have hR2 : (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2) ≤ 2 * Ptot := by
    rw [hPtot]; linarith [hF4, hslab]
  have hid : ∀ X : ℝ, 3 * t ^ 4 * ((1 / 3) * (1 / t ^ 4) * X) = X := by
    intro X; field_simp
  have hbig := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 3 * t ^ 4 by positivity)
  rw [hid] at hbig
  have hexpand : 3 * t ^ 4 * (t * Qtot
        + (1 / t ^ 2) * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + 3 * (1 / t ^ 2) * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2))
      = 3 * t ^ 5 * Qtot
        + 3 * t ^ 2 * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + 9 * t ^ 2 * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2) := by
    field_simp; ring
  rw [hexpand] at hbig
  have hA : 3 * t ^ 2 * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
      ≤ 3 * t ^ 2 * (2 * Ptot) :=
    mul_le_mul_of_nonneg_left hR2 (by positivity)
  have hBc : 9 * t ^ 2 * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2)
      ≤ 9 * t ^ 2 * (6 * Sin) :=
    mul_le_mul_of_nonneg_left hF2 (by positivity)
  have hSinP : 54 * t ^ 2 * Sin ≤ 54 * t ^ 2 * (blockPoincareSharpConst ell * Ptot) :=
    mul_le_mul_of_nonneg_left hSinC (by positivity)
  have hbc : bcoef ell (blockPoincareSharpConst ell)
      = 6 * t ^ 2 + (54 * t ^ 2 + 1) * blockPoincareSharpConst ell := by
    unfold bcoef; rw [hT]
  rw [hbc]
  nlinarith [hbig, hF1, hA, hBc, hSinP, hSinC, hPnn, hSinnn]

/-- **THE DELIVERED `(2.128)`: `ell·Σ_c|(Q₁B)(c)|² + Σ_p|(∂₁B)(p)|² ≥ (1/54)·ell^{-5}·‖B‖²`** for
every `ell ≥ 2`, versus `Lemma24GeneralEll.lemma24_general_ell`'s `(1/180)·ell^{-5}`.  Same
exponent; the constant improves by exactly `180/54 = 10/3`, which is the `(2.123)` improvement
propagated. -/
theorem lemma24_sharpened (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B
      ≥ (1 / 54) * (1 / (ell : ℝ) ^ 5) * bondNormSq B := by
  set t : ℝ := (ell : ℝ) with hT
  have ht0 : (0 : ℝ) < t := by
    rw [hT]; exact_mod_cast (show 0 < ell by omega)
  have ht2 : (2 : ℝ) ≤ t := by rw [hT]; exact_mod_cast hell2
  set N := bondNormSq B with hN
  set Ptot := totalCurlEnergy B with hPtot
  set Qtot := coarseQEnergy ell B with hQtot
  have hPnn : (0 : ℝ) ≤ Ptot := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQnn : (0 : ℝ) ≤ Qtot := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hMain := sharp_size_bound hell2 hstrict hdvd B hB
  rw [← hN, ← hPtot, ← hQtot, ← hT] at hMain
  have hbcle : bcoef ell (blockPoincareSharpConst ell) ≤ 54 * t ^ 5 := by
    rw [hT]; exact sharp_bcoef_le ell hell2
  rw [ge_iff_le, ← sub_nonneg]
  have hkey : t * Qtot + Ptot - (1 / 54) * (1 / t ^ 5) * N
      = (54 * t ^ 5 * (t * Qtot + Ptot) - N) / (54 * t ^ 5) := by
    field_simp
  rw [hkey]
  refine div_nonneg ?_ (by positivity)
  have hc1 : (0 : ℝ) ≤ 54 * t ^ 6 - 3 * t ^ 5 := by nlinarith [ht2, pow_pos ht0 5]
  have hc2 : (0 : ℝ) ≤ 54 * t ^ 5 - bcoef ell (blockPoincareSharpConst ell) := by linarith
  nlinarith [hMain, mul_nonneg hc1 hQnn, mul_nonneg hc2 hPnn]

/-- **AND THE FULL PRINTED `(2.128)` AT `ell = 3`.**  `Lemma24Conclusion 3 B`, i.e. Bałaban's own
`(1/108)·ell^{-4}` with the printed exponent `L^{-d-1}`, on any torus with `3 < L ν + 1` and
`3 ∣ L ν + 1`.  Previously available only at `ell = 2`
(`HrefReduction.lemma24_unconditional_U1_ell2_uncond`); it follows here because the sharpened
`(2.123)` constant at `ell = 3` is `16`, and `bcoef 3 16 = 7846 ≤ 8748 = 108·3⁴`
(`sharp_const_meets_requirement_ell3`). -/
theorem lemma24_printed_ell3
    (hstrict : ∀ ν : Fin 3, (3 : ℕ) < L ν + 1) (hdvd : ∀ ν : Fin 3, (3 : ℕ) ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 3) :
    Lemma24Conclusion (L := L) 3 B := by
  have hMain := sharp_size_bound (L := L) (ell := 3) (by norm_num) hstrict hdvd B hB
  have hbc : bcoef 3 (blockPoincareSharpConst (3 : ℕ)) = 7846 :=
    sharp_const_meets_requirement_ell3.1
  rw [hbc] at hMain
  have hPnn : (0 : ℝ) ≤ totalCurlEnergy B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQnn : (0 : ℝ) ≤ coarseQEnergy 3 B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Lemma24Conclusion, ge_iff_le]
  have hnum : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [hnum] at hMain ⊢
  norm_num at hMain ⊢
  nlinarith [hMain, hPnn, hQnn]

/-- **The printed `(2.128)` at `ell = 2`, re-proved by THIS route.**  `HrefReduction.
lemma24_unconditional_U1_ell2_uncond` already has `Lemma24Conclusion 2 B` via the BlochPSD /
reflection / reindex chain; this is an INDEPENDENT proof of the same statement through the
sharpened `(2.123)` + Bałaban's assembly, sharing none of that chain.  Arithmetic:
`bcoef 2 3 = 675 ≤ 1728 = 108·2⁴` (`sharp_const_meets_requirement_ell2`). -/
theorem lemma24_printed_ell2
    (hstrict : ∀ ν : Fin 3, (2 : ℕ) < L ν + 1) (hdvd : ∀ ν : Fin 3, (2 : ℕ) ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2) :
    Lemma24Conclusion (L := L) 2 B := by
  have hMain := sharp_size_bound (L := L) (ell := 2) (by norm_num) hstrict hdvd B hB
  have hbc : bcoef 2 (blockPoincareSharpConst (2 : ℕ)) = 675 :=
    sharp_const_meets_requirement_ell2.1
  rw [hbc] at hMain
  have hPnn : (0 : ℝ) ≤ totalCurlEnergy B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQnn : (0 : ℝ) ≤ coarseQEnergy 2 B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Lemma24Conclusion, ge_iff_le]
  have hnum : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hnum] at hMain ⊢
  norm_num at hMain ⊢
  nlinarith [hMain, hPnn, hQnn]

#print axioms lemma24_printed_ell2

/-- **The improvement, stated as an inequality between the two delivered constants** — `10/3`. -/
theorem lemma24_sharpened_improves :
    (1 / 180 : ℝ) < 1 / 54 ∧ (1 / 54 : ℝ) / (1 / 180) = 10 / 3 := by
  constructor <;> norm_num

#print axioms sharp_size_bound
#print axioms lemma24_sharpened
#print axioms lemma24_printed_ell3
#print axioms lemma24_sharpened_improves

end Assembly

/-! ## §7. THE SHARPNESS WITNESS — an admissible field whose `(2.123)` ratio grows like `ell³`.

The extremal direction of the block Rayleigh quotient (found numerically in
`compute/block_poincare_sharp/extremal.py`, then read off in closed form) is NOT a counting
artifact: it is an exact CANCELLATION.  Take (block coordinates; Bałaban's axial `e_1` is direction
`0`, and `y` is any coarse centre so every `(y μ).val` is a multiple of `ell`)

>   `B(x,0) = 0`
>   `B(x,1) = 0` if `x_0 ≡ 0 (mod ell)`, else `H(x_2 mod ell)`
>   `B(x,2) = −2·(x_1 mod ell)·H(x_2 mod ell)`,   `H(m) = (−1)^m`

Then, on every plaquette inside a block:
* the `(0,2)`-curl vanishes identically (`B(·,2)` does not depend on `x_0`);
* the `(0,1)`-curl vanishes unless `x_0 ≡ 0`, where it is `H`;
* the `(1,2)`-curl is `∂_1B_2 − ∂_2B_1 = −2H − (−2H) = 0` unless `x_0 ≡ 0`, where it is `−2H`.

So the ENTIRE curl energy of the block sits on the single axial plane `x_0 = y_0` — precisely the
plane through which Bałaban's leg B routes every bond, and the direction-`1` component is tuned to
cancel the `(1,2)`-curl everywhere else.  Meanwhile `Σ_b|B|²` collects `(x_1 − y_1)²` over the whole
block, which is `Θ(ell³)` per `(x_0,x_2)` pair.  The ratio is therefore `Θ(ell³)`, not `O(ell²)`. -/

section Sharpness

/-- `H(m) = (−1)^m`. -/
def hAlt (m : ℕ) : ℝ := if m % 2 = 0 then 1 else -1

theorem hAlt_succ (m : ℕ) : hAlt (m + 1) = - hAlt m := by
  unfold hAlt
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h1 : (m + 1) % 2 = 1 := by omega
    rw [h, h1]; norm_num
  · have h1 : (m + 1) % 2 = 0 := by omega
    rw [h, h1]; norm_num

theorem hAlt_sq (m : ℕ) : (hAlt m) ^ 2 = 1 := by
  unfold hAlt; split <;> norm_num

/-- Inside a block anchored at a coarse centre, the residue mod `ell` IS the block offset. -/
theorem coord_mod (ell y x : ℕ) (hy : y % ell = 0) (h1 : y ≤ x) (h2 : x < y + ell) :
    x % ell = x - y := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hy
  subst hq
  set a := ell * q with ha
  have hx : a + (x - a) = x := by omega
  calc x % ell = (a + (x - a)) % ell := by rw [hx]
    _ = (x - a) % ell := by rw [ha]; exact Nat.mul_add_mod _ _ _
    _ = x - a := Nat.mod_eq_of_lt (by omega)

/-- **The sharpness witness.** Periodic in each coordinate with period `ell`, so it is admissible
for EVERY coarse centre simultaneously (`sw_mem`), not just one block. -/
noncomputable def sw (ell : ℕ) (b : Bond L) : ℝ :=
  if b.2 = 1 then
    (if (b.1 0).val % ell = 0 then 0 else hAlt ((b.1 2).val % ell))
  else if b.2 = 2 then
    (-2 : ℝ) * (((b.1 1).val % ell : ℕ) : ℝ) * hAlt ((b.1 2).val % ell)
  else 0

theorem sw_dir0 (ell : ℕ) (b : Bond L) (h : b.2 = 0) : sw ell b = 0 := by
  unfold sw
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

theorem sw_dir1_axial (ell : ℕ) (b : Bond L) (h : b.2 = 1) (h0 : (b.1 0).val % ell = 0) :
    sw ell b = 0 := by
  unfold sw; rw [if_pos h, if_pos h0]

theorem sw_dir2_axial (ell : ℕ) (b : Bond L) (h : b.2 = 2) (h1 : (b.1 1).val % ell = 0) :
    sw ell b = 0 := by
  unfold sw
  rw [if_neg (by rw [h]; decide), if_pos h, h1]
  norm_num

/-- **The witness is `(2.121)`-admissible for every block** — each of the three axis segments of
`Γ_{y,x}` lands in one of the three vanishing classes above:
direction-`0` bonds (`sw_dir0`); direction-`1` bonds pinned to `x_0 = y_0` (`sw_dir1_axial`);
direction-`2` bonds pinned to `x_1 = y_1` (`sw_dir2_axial`). -/
theorem sw_mem (ell : ℕ) : sw (L := L) ell ∈ admissibleSubspaceInter L ell := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x hx b hb
  rw [mem_CoarseLattice] at hy
  unfold staircasePath at hb
  rw [Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (hb2 | hb1) | hb0
  · -- the direction-`2` segment, based at `y`: its coordinate `1` equals `y 1`
    rw [mem_axisSegment] at hb2
    obtain ⟨hdir, hpin, _, _⟩ := hb2
    have h1 : b.1 1 = y 1 := hpin 1 (by decide)
    exact sw_dir2_axial ell b hdir (by rw [h1]; exact hy 1)
  · -- the direction-`1` segment, based at `corner1 y x`: its coordinate `0` equals `y 0`
    rw [mem_axisSegment] at hb1
    obtain ⟨hdir, hpin, _, _⟩ := hb1
    have h0 : b.1 0 = (corner1 y x) 0 := hpin 0 (by decide)
    have hc : (corner1 y x) 0 = y 0 := Function.update_of_ne (by decide) _ _
    exact sw_dir1_axial ell b hdir (by rw [h0, hc]; exact hy 0)
  · rw [mem_axisSegment] at hb0
    exact sw_dir0 ell b hb0.1

/-! ### The curl of the witness: supported on the single axial plane `x_0 = y_0`. -/

/-- The three shift-coordinate facts used below, packaged for an in-block plaquette. -/
theorem plaq_coords {ell : ℕ}
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (x : PeriodicLatticeSite L)
    (hx : x ∈ blockOf y ell) (μ : Fin 3) (hμ : (x μ).val + 1 < (y μ).val + ell) :
    ((periodicLatticeShift x μ) μ).val % ell = (x μ).val % ell + 1 := by
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  have hy' := mem_CoarseLattice.mp hy
  have hge := (mem_blockOf.mp hx) μ |>.1
  have hno : (x μ).val + 1 < L μ + 1 := by omega
  rw [AdalyFormal.Balaban.PoincareBridge.shift_val_self x μ hno]
  rw [coord_mod ell (y μ).val ((x μ).val + 1) (hy' μ) (by omega) (by omega),
    coord_mod ell (y μ).val (x μ).val (hy' μ) hge (by omega)]
  omega

/-- The residue of an in-block coordinate is its offset, and it is `< ell`. -/
theorem block_coord_mod {ell : ℕ} {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell)
    (μ : Fin 3) : (x μ).val % ell = (x μ).val - (y μ).val := by
  have hy' := mem_CoarseLattice.mp hy
  exact coord_mod ell (y μ).val (x μ).val (hy' μ) ((mem_blockOf.mp hx) μ).1
    ((mem_blockOf.mp hx) μ).2

/-- For an in-block plaquette, both of its directions can be stepped without leaving the block. -/
theorem plaq_shift_bound {ell : ℕ} (hstrict : ∀ ν : Fin 3, ell < L ν + 1)
    {y : PeriodicLatticeSite L} {p : PeriodicLatticePlaquette L} (hp : p ∈ plaqsInBlock y ell) :
    (p.1 p.2.1.1).val + 1 < (y p.2.1.1).val + ell
      ∧ (p.1 p.2.1.2).val + 1 < (y p.2.1.2).val + ell := by
  obtain ⟨hbase, hsμ, hsν, _⟩ := mem_plaqsInBlock.mp hp
  constructor
  · have hno := noWrap_of_bondInBlock (hstrict p.2.1.1) hbase hsμ
    have hv := AdalyFormal.Balaban.PoincareBridge.shift_val_self p.1 p.2.1.1 hno
    have hlt := (mem_blockOf.mp hsμ) p.2.1.1 |>.2
    rw [hv] at hlt; exact hlt
  · have hno := noWrap_of_bondInBlock (hstrict p.2.1.2) hbase hsν
    have hv := AdalyFormal.Balaban.PoincareBridge.shift_val_self p.1 p.2.1.2 hno
    have hlt := (mem_blockOf.mp hsν) p.2.1.2 |>.2
    rw [hv] at hlt; exact hlt

/-- **THE CURL OF THE WITNESS.**  On every plaquette inside a block the curl either VANISHES, or
the plaquette sits on the single axial plane `x_0 ≡ y_0` and the curl has square `≤ 4`.  The
`(0,2)`-curl vanishes unconditionally; the `(0,1)`- and `(1,2)`-curls vanish off the axial plane —
the latter by the exact cancellation `∂₁B₂ − ∂₂B₁ = −2H − (−2H) = 0`. -/
theorem sw_dir1_val (ell : ℕ) (x : PeriodicLatticeSite L) :
    sw ell (x, (1 : Fin 3)) = if (x 0).val % ell = 0 then 0 else hAlt ((x 2).val % ell) := by
  unfold sw; rw [if_pos rfl]

theorem sw_dir2_val (ell : ℕ) (x : PeriodicLatticeSite L) :
    sw ell (x, (2 : Fin 3)) = (-2 : ℝ) * (((x 1).val % ell : ℕ) : ℝ) * hAlt ((x 2).val % ell) := by
  unfold sw
  rw [if_neg (by decide : ¬ ((2 : Fin 3) = 1)), if_pos rfl]

theorem sw_dir0_val (ell : ℕ) (x : PeriodicLatticeSite L) : sw ell (x, (0 : Fin 3)) = 0 :=
  sw_dir0 ell (x, (0 : Fin 3)) rfl

def dir01 : PeriodicPlaquetteDirections := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩
def dir02 : PeriodicPlaquetteDirections := ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩

theorem plaq_dir_cases (q : PeriodicPlaquetteDirections) :
    q = dir01 ∨ q = dir02 ∨ q = dir12 := by
  revert q; unfold dir01 dir02 dir12; decide

/-- `(0,1)`-plane: the curl is `H` on the axial plane and `0` elsewhere. -/
theorem sw_curl01 (ell : ℕ) (x : PeriodicLatticeSite L)
    (hstep0 : ((periodicLatticeShift x 0) 0).val % ell = (x 0).val % ell + 1) :
    curlValue (sw ell) (x, dir01)
      = (if (x 0).val % ell = 0 then hAlt ((x 2).val % ell) else 0) := by
  have hc2 : (periodicLatticeShift x 0) 2 = x 2 :=
    periodicLatticeShift_coord_ne x (by decide : (2 : Fin 3) ≠ 0)
  have h1 : curlValue (sw ell) (x, dir01)
      = sw ell (x, (0 : Fin 3)) + sw ell (periodicLatticeShift x 0, (1 : Fin 3))
        - sw ell (periodicLatticeShift x 1, (0 : Fin 3)) - sw ell (x, (1 : Fin 3)) := rfl
  rw [h1, sw_dir0_val, sw_dir0_val, sw_dir1_val, sw_dir1_val, hstep0, hc2,
    if_neg (by omega : ¬ ((x 0).val % ell + 1 = 0))]
  by_cases h : (x 0).val % ell = 0
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- `(0,2)`-plane: the curl vanishes identically — `B(·,2)` does not depend on coordinate `0`. -/
theorem sw_curl02 (ell : ℕ) (x : PeriodicLatticeSite L) :
    curlValue (sw ell) (x, dir02) = 0 := by
  have hc1 : (periodicLatticeShift x 0) 1 = x 1 :=
    periodicLatticeShift_coord_ne x (by decide : (1 : Fin 3) ≠ 0)
  have hc2 : (periodicLatticeShift x 0) 2 = x 2 :=
    periodicLatticeShift_coord_ne x (by decide : (2 : Fin 3) ≠ 0)
  have h1 : curlValue (sw ell) (x, dir02)
      = sw ell (x, (0 : Fin 3)) + sw ell (periodicLatticeShift x 0, (2 : Fin 3))
        - sw ell (periodicLatticeShift x 2, (0 : Fin 3)) - sw ell (x, (2 : Fin 3)) := rfl
  rw [h1, sw_dir0_val, sw_dir0_val, sw_dir2_val, sw_dir2_val, hc1, hc2]
  ring

/-- `(1,2)`-plane — **THE CANCELLATION.**  `∂₁B₂ = −2H` and `∂₂B₁ = −2H` off the axial plane, so
the curl is `0` there; on the axial plane `∂₂B₁ = 0` and the curl is `−2H`. -/
theorem sw_curl12 (ell : ℕ) (x : PeriodicLatticeSite L)
    (hstep1 : ((periodicLatticeShift x 1) 1).val % ell = (x 1).val % ell + 1)
    (hstep2 : ((periodicLatticeShift x 2) 2).val % ell = (x 2).val % ell + 1) :
    curlValue (sw ell) (x, dir12)
      = (if (x 0).val % ell = 0 then (-2 : ℝ) * hAlt ((x 2).val % ell) else 0) := by
  have ha2 : (periodicLatticeShift x 1) 2 = x 2 :=
    periodicLatticeShift_coord_ne x (by decide : (2 : Fin 3) ≠ 1)
  have hb0 : (periodicLatticeShift x 2) 0 = x 0 :=
    periodicLatticeShift_coord_ne x (by decide : (0 : Fin 3) ≠ 2)
  have h1 : curlValue (sw ell) (x, dir12)
      = sw ell (x, (1 : Fin 3)) + sw ell (periodicLatticeShift x 1, (2 : Fin 3))
        - sw ell (periodicLatticeShift x 2, (1 : Fin 3)) - sw ell (x, (2 : Fin 3)) := rfl
  rw [h1, sw_dir1_val, sw_dir1_val, sw_dir2_val, sw_dir2_val, hstep1, hstep2, ha2, hb0]
  rw [hAlt_succ]
  by_cases h : (x 0).val % ell = 0
  · rw [if_pos h, if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h, if_neg h]; push_cast; ring

/-- **THE CURL OF THE WITNESS.**  On every plaquette inside a block the curl either VANISHES, or
the plaquette sits on the single axial plane `x_0 ≡ y_0 (mod ell)` and the curl has square `≤ 4`. -/
theorem sw_curl_dichotomy {ell : ℕ}
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1)) (hstrict : ∀ ν : Fin 3, ell < L ν + 1)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {p : PeriodicLatticePlaquette L} (hp : p ∈ plaqsInBlock y ell) :
    curlValue (sw ell) p = 0
      ∨ ((p.1 0).val % ell = 0 ∧ (curlValue (sw ell) p) ^ 2 ≤ 4) := by
  obtain ⟨hbase, _, _, _⟩ := mem_plaqsInBlock.mp hp
  obtain ⟨hbμ, hbν⟩ := plaq_shift_bound hstrict hp
  have hpair : p = (p.1, p.2) := rfl
  rcases plaq_dir_cases p.2 with hd | hd | hd
  · have hdd : p.2.1.1 = 0 ∧ p.2.1.2 = 1 := by rw [hd]; exact ⟨rfl, rfl⟩
    rw [hdd.1] at hbμ
    have hstep0 := plaq_coords hdvd hy p.1 hbase 0 hbμ
    have heq : curlValue (sw ell) p = curlValue (sw ell) (p.1, dir01) := by rw [← hd]
    rw [heq, sw_curl01 ell p.1 hstep0]
    by_cases h : (p.1 0).val % ell = 0
    · refine Or.inr ⟨h, ?_⟩
      rw [if_pos h, hAlt_sq]; norm_num
    · exact Or.inl (if_neg h)
  · have heq : curlValue (sw ell) p = curlValue (sw ell) (p.1, dir02) := by rw [← hd]
    exact Or.inl (by rw [heq, sw_curl02])
  · have hdd : p.2.1.1 = 1 ∧ p.2.1.2 = 2 := by rw [hd]; exact ⟨rfl, rfl⟩
    rw [hdd.1] at hbμ
    rw [hdd.2] at hbν
    have hstep1 := plaq_coords hdvd hy p.1 hbase 1 hbμ
    have hstep2 := plaq_coords hdvd hy p.1 hbase 2 hbν
    have heq : curlValue (sw ell) p = curlValue (sw ell) (p.1, dir12) := by rw [← hd]
    rw [heq, sw_curl12 ell p.1 hstep1 hstep2]
    by_cases h : (p.1 0).val % ell = 0
    · refine Or.inr ⟨h, ?_⟩
      rw [if_pos h]
      have : ((-2 : ℝ) * hAlt ((p.1 2).val % ell)) ^ 2 = 4 * (hAlt ((p.1 2).val % ell)) ^ 2 := by
        ring
      rw [this, hAlt_sq]; norm_num
    · exact Or.inl (if_neg h)

#print axioms hAlt_succ
#print axioms coord_mod
#print axioms sw_mem
#print axioms sw_curl01
#print axioms sw_curl02
#print axioms sw_curl12
#print axioms sw_curl_dichotomy

/-! ### The curl energy of a block: at most `12·ell²`, because it lives on ONE plane. -/

/-- The axial plane inside the block — the only place the witness's curl is nonzero. -/
def axialPlaqs (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticePlaquette L) :=
  (plaqsInBlock y ell).filter (fun p => (p.1 0).val % ell = 0)

/-- `|axial plane| ≤ 3·ell²`: coordinate `0` is PINNED to `y_0`, so only two coordinates and the
three plane labels remain free. -/
theorem axialPlaqs_card {ell : ℕ} {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (axialPlaqs y ell).card ≤ 3 * ell ^ 2 := by
  have hcard : (Finset.range ell ×ˢ (Finset.range ell ×ˢ
      (Finset.univ : Finset PeriodicPlaquetteDirections))).card = 3 * ell ^ 2 := by
    have h3 : (Finset.univ : Finset PeriodicPlaquetteDirections).card = 3 := by decide
    rw [Finset.card_product, Finset.card_product, Finset.card_range, h3]
    ring
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun p : PeriodicLatticePlaquette L =>
      ((p.1 1).val - (y 1).val, ((p.1 2).val - (y 2).val, p.2)))
  · intro p hp
    unfold axialPlaqs at hp
    obtain ⟨hpb, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hbase, _, _, _⟩ := mem_plaqsInBlock.mp hpb
    have h1 := (mem_blockOf.mp hbase) 1
    have h2 := (mem_blockOf.mp hbase) 2
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega, Finset.mem_univ _⟩
  · intro p hp p' hp' heq
    rw [Finset.mem_coe] at hp hp'
    unfold axialPlaqs at hp hp'
    obtain ⟨hpb, hax⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpb', hax'⟩ := Finset.mem_filter.mp hp'
    obtain ⟨hbase, _, _, _⟩ := mem_plaqsInBlock.mp hpb
    obtain ⟨hbase', _, _, _⟩ := mem_plaqsInBlock.mp hpb'
    -- coordinate 0 is pinned
    have hm0 : (p.1 0).val - (y 0).val = 0 := by
      rw [← block_coord_mod hy hbase 0]; exact hax
    have hm0' : (p'.1 0).val - (y 0).val = 0 := by
      rw [← block_coord_mod hy hbase' 0]; exact hax'
    have hg0 := (mem_blockOf.mp hbase) 0 |>.1
    have hg0' := (mem_blockOf.mp hbase') 0 |>.1
    have hg1 := (mem_blockOf.mp hbase) 1 |>.1
    have hg1' := (mem_blockOf.mp hbase') 1 |>.1
    have hg2 := (mem_blockOf.mp hbase) 2 |>.1
    have hg2' := (mem_blockOf.mp hbase') 2 |>.1
    have he1 : (p.1 1).val - (y 1).val = (p'.1 1).val - (y 1).val := congrArg Prod.fst heq
    have he2 : (p.1 2).val - (y 2).val = (p'.1 2).val - (y 2).val :=
      congrArg (fun q => q.2.1) heq
    have hedir : p.2 = p'.2 := congrArg (fun q => q.2.2) heq
    have hsite : p.1 = p'.1 := by
      funext μ
      by_cases hμ0 : μ = 0
      · subst hμ0; exact Fin.ext (by omega)
      · by_cases hμ1 : μ = 1
        · subst hμ1; exact Fin.ext (by omega)
        · have hμ2 : μ = 2 := by
            have := μ.isLt
            have ha : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
            have hb : μ.val ≠ 1 := fun h => hμ1 (Fin.ext h)
            apply Fin.ext; omega
          subst hμ2; exact Fin.ext (by omega)
    exact Prod.ext hsite hedir

/-- **The witness's block curl energy is `≤ 12·ell²`** — `O(ell²)`, not `O(ell³)`, because the
cancellation confines it to a single plane. -/
theorem sw_rhs_le {ell : ℕ}
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1)) (hstrict : ∀ ν : Fin 3, ell < L ν + 1)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    ∑ p ∈ plaqsInBlock y ell, (curlValue (sw ell) p) ^ 2 ≤ 12 * (ell : ℝ) ^ 2 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (plaqsInBlock y ell)
    (fun p => (p.1 0).val % ell = 0) (fun p => (curlValue (sw (L := L) ell) p) ^ 2)
  have hzero : ∑ p ∈ (plaqsInBlock y ell).filter (fun p => ¬ ((p.1 0).val % ell = 0)),
      (curlValue (sw (L := L) ell) p) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨hpb, hnax⟩ := Finset.mem_filter.mp hp
    rcases sw_curl_dichotomy hdvd hstrict hy hpb with h | ⟨hax, _⟩
    · rw [h]; ring
    · exact absurd hax hnax
  have hax : ∑ p ∈ axialPlaqs y ell, (curlValue (sw (L := L) ell) p) ^ 2
      ≤ ((axialPlaqs y ell).card : ℝ) * 4 := by
    have hb : ∀ p ∈ axialPlaqs y ell, (curlValue (sw (L := L) ell) p) ^ 2 ≤ (4 : ℝ) := by
      intro p hp
      unfold axialPlaqs at hp
      obtain ⟨hpb, _⟩ := Finset.mem_filter.mp hp
      rcases sw_curl_dichotomy hdvd hstrict hy hpb with h | ⟨_, h⟩
      · rw [h]; norm_num
      · exact h
    have := Finset.sum_le_card_nsmul (axialPlaqs y ell)
      (fun p => (curlValue (sw (L := L) ell) p) ^ 2) 4 hb
    simpa [nsmul_eq_mul, mul_comm] using this
  have hcard : ((axialPlaqs y ell).card : ℝ) ≤ 3 * (ell : ℝ) ^ 2 := by
    have h := axialPlaqs_card (L := L) (ell := ell) hy
    have : ((axialPlaqs y ell).card : ℝ) ≤ ((3 * ell ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  unfold axialPlaqs at hax hcard
  linarith [hsplit, hzero, hax, hcard]

/-! ### The bond energy of a block: at least `(2/3)·ell²(ell−1)²(2ell−1)`, i.e. `Θ(ell⁵)`. -/

theorem sum_sq_range (n : ℕ) :
    6 * ∑ j ∈ Finset.range n, ((j : ℝ)) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linear_combination ih

/-- The three block offsets, as a function on directions. -/
def blkOff (a j m : ℕ) (μ : Fin 3) : ℕ := if μ = 0 then a else if μ = 1 then j else m

theorem blkOff_lt {ell a j m : ℕ} (ha : a < ell) (hj : j < ell) (hm : m < ell) (μ : Fin 3) :
    blkOff a j m μ < ell := by
  unfold blkOff
  split
  · exact ha
  · split
    · exact hj
    · exact hm

theorem blkOff_zero (a j m : ℕ) : blkOff a j m 0 = a := by
  unfold blkOff; rw [if_pos rfl]

theorem blkOff_one (a j m : ℕ) : blkOff a j m 1 = j := by
  unfold blkOff; rw [if_neg (by decide : ¬ ((1 : Fin 3) = 0)), if_pos rfl]

theorem blkOff_two (a j m : ℕ) : blkOff a j m 2 = m := by
  unfold blkOff
  rw [if_neg (by decide : ¬ ((2 : Fin 3) = 0)), if_neg (by decide : ¬ ((2 : Fin 3) = 1))]

/-- The site of `blockOf y ell` at offsets `(a,j,m)`. -/
def blkSite (y : PeriodicLatticeSite L) (a j m : ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨((y μ).val + blkOff a j m μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem blkSite_val {ell : ℕ} {y : PeriodicLatticeSite L}
    (hfit : ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1) {a j m : ℕ}
    (ha : a < ell) (hj : j < ell) (hm : m < ell) (μ : Fin 3) :
    (blkSite y a j m μ).val = (y μ).val + blkOff a j m μ := by
  have hoff := blkOff_lt ha hj hm μ
  have hlt : (y μ).val + blkOff a j m μ < L μ + 1 := by have := hfit μ; omega
  show ((y μ).val + blkOff a j m μ) % (L μ + 1) = _
  exact Nat.mod_eq_of_lt hlt

theorem blkSite_mem {ell : ℕ} {y : PeriodicLatticeSite L}
    (hfit : ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1) {a j m : ℕ}
    (ha : a < ell) (hj : j < ell) (hm : m < ell) : blkSite y a j m ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  rw [blkSite_val hfit ha hj hm μ]
  exact ⟨Nat.le_add_right _ _, by have := blkOff_lt ha hj hm μ; omega⟩

/-- The direction-`2` bond at offsets `(a,j,m)` lies wholly inside the block when `m + 1 < ell`. -/
theorem blkBond_mem {ell : ℕ} {y : PeriodicLatticeSite L}
    (hfit : ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1) {a j m : ℕ}
    (ha : a < ell) (hj : j < ell) (hm : m + 1 < ell) :
    bondInBlock y ell ((blkSite y a j m : PeriodicLatticeSite L), (2 : Fin 3)) := by
  have hmlt : m < ell := by omega
  refine ⟨blkSite_mem hfit ha hj hmlt, ?_⟩
  have hv2 : (blkSite y a j m 2).val = (y 2).val + m := by
    rw [blkSite_val hfit ha hj hmlt 2, blkOff_two]
  have hno : (blkSite y a j m (2 : Fin 3)).val + 1 < L 2 + 1 := by
    rw [hv2]; have := hfit 2; omega
  rw [mem_blockOf]
  intro μ
  by_cases hμ : μ = 2
  · subst hμ
    rw [AdalyFormal.Balaban.PoincareBridge.shift_val_self _ (2 : Fin 3) hno, hv2]
    exact ⟨by omega, by omega⟩
  · rw [periodicLatticeShift_coord_ne _ hμ, blkSite_val hfit ha hj hmlt μ]
    exact ⟨Nat.le_add_right _ _, by have := blkOff_lt ha hj hmlt μ; omega⟩

/-- The witness's value on that bond: `4·j²` after squaring — the `x_1`-ramp. -/
theorem sw_blkBond_sq {ell : ℕ} {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (hfit : ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1) {a j m : ℕ}
    (ha : a < ell) (hj : j < ell) (hm : m < ell) :
    (sw ell ((blkSite y a j m : PeriodicLatticeSite L), (2 : Fin 3))) ^ 2 = 4 * (j : ℝ) ^ 2 := by
  have hy' := mem_CoarseLattice.mp hy
  have hv1 : (blkSite y a j m 1).val = (y 1).val + j := by
    rw [blkSite_val hfit ha hj hm 1, blkOff_one]
  have hmod1 : (blkSite y a j m (1 : Fin 3)).val % ell = j := by
    rw [hv1, coord_mod ell (y 1).val ((y 1).val + j) (hy' 1) (by omega) (by omega)]
    omega
  rw [sw_dir2_val, hmod1]
  have h4 : ((-2 : ℝ) * ((j : ℕ) : ℝ) * hAlt ((blkSite y a j m (2 : Fin 3)).val % ell)) ^ 2
      = 4 * (j : ℝ) ^ 2 * (hAlt ((blkSite y a j m (2 : Fin 3)).val % ell)) ^ 2 := by
    ring
  rw [h4, hAlt_sq]; ring

/-- **The witness's block bond energy is at least `(2/3)·ell²(ell−1)²(2ell−1)`** — `Θ(ell⁵)`,
because it collects the squared `x_1`-offset over the WHOLE block. -/
theorem sw_lhs_ge {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (2 / 3 : ℝ) * (ell : ℝ) ^ 2 * ((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1)
      ≤ ∑ b ∈ bondsInBlock y ell, (sw ell b) ^ 2 := by
  have hfit : ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1 := fun μ => coarseLattice_mem_fits hdvd hy μ
  set s : Finset (ℕ × ℕ × ℕ) :=
    Finset.range ell ×ˢ (Finset.range ell ×ˢ Finset.range (ell - 1)) with hs
  set Φ : ℕ × ℕ × ℕ → Bond L :=
    fun t => ((blkSite y t.1 t.2.1 t.2.2 : PeriodicLatticeSite L), (2 : Fin 3)) with hΦ
  have hmem : ∀ t ∈ s, Φ t ∈ bondsInBlock y ell := by
    intro t ht
    rw [hs, Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range,
      Finset.mem_range] at ht
    rw [mem_bondsInBlock]
    exact blkBond_mem hfit ht.1 ht.2.1 (by omega)
  have hinj : Set.InjOn Φ (s : Set (ℕ × ℕ × ℕ)) := by
    intro t ht t' ht' heq
    rw [Finset.mem_coe, hs, Finset.mem_product, Finset.mem_product, Finset.mem_range,
      Finset.mem_range, Finset.mem_range] at ht ht'
    have hsite : (blkSite y t.1 t.2.1 t.2.2 : PeriodicLatticeSite L)
        = blkSite y t'.1 t'.2.1 t'.2.2 := congrArg Prod.fst heq
    have hv : ∀ μ : Fin 3, (blkSite y t.1 t.2.1 t.2.2 μ).val
        = (blkSite y t'.1 t'.2.1 t'.2.2 μ).val := fun μ => by rw [hsite]
    have e0 := hv 0; have e1 := hv 1; have e2 := hv 2
    rw [blkSite_val hfit ht.1 ht.2.1 (by omega) 0,
      blkSite_val hfit ht'.1 ht'.2.1 (by omega) 0] at e0
    rw [blkSite_val hfit ht.1 ht.2.1 (by omega) 1,
      blkSite_val hfit ht'.1 ht'.2.1 (by omega) 1] at e1
    rw [blkSite_val hfit ht.1 ht.2.1 (by omega) 2,
      blkSite_val hfit ht'.1 ht'.2.1 (by omega) 2] at e2
    rw [blkOff_zero, blkOff_zero] at e0
    rw [blkOff_one, blkOff_one] at e1
    rw [blkOff_two, blkOff_two] at e2
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  have hsub : s.image Φ ⊆ bondsInBlock y ell := by
    intro b hb
    obtain ⟨t, ht, hbt⟩ := Finset.mem_image.mp hb
    rw [← hbt]; exact hmem t ht
  have hstep1 : ∑ b ∈ s.image Φ, (sw (L := L) ell b) ^ 2
      ≤ ∑ b ∈ bondsInBlock y ell, (sw (L := L) ell b) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hval : ∑ b ∈ s.image Φ, (sw (L := L) ell b) ^ 2
      = ∑ t ∈ s, 4 * ((t.2.1 : ℕ) : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun t ht t' ht' h => hinj (by exact ht) (by exact ht') h)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hs, Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range,
      Finset.mem_range] at ht
    exact sw_blkBond_sq hy hfit ht.1 ht.2.1 (by omega)
  have hprod : ∑ t ∈ s, 4 * ((t.2.1 : ℕ) : ℝ) ^ 2
      = (ell : ℝ) * (((ell - 1 : ℕ)) : ℝ) * (4 * ∑ j ∈ Finset.range ell, ((j : ℝ)) ^ 2) := by
    rw [hs, Finset.sum_product]
    have e1 : ∀ a : ℕ,
        (∑ u ∈ Finset.range ell ×ˢ Finset.range (ell - 1), 4 * ((u.1 : ℕ) : ℝ) ^ 2)
          = ((ell - 1 : ℕ) : ℝ) * (4 * ∑ j ∈ Finset.range ell, ((j : ℝ)) ^ 2) := by
      intro a
      rw [Finset.sum_product]
      have e2 : ∀ j : ℕ, (∑ _m ∈ Finset.range (ell - 1), 4 * ((j : ℕ) : ℝ) ^ 2)
          = ((ell - 1 : ℕ) : ℝ) * (4 * ((j : ℝ)) ^ 2) := by
        intro j
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_congr rfl (fun j _ => e2 j), ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => e1 a), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have hcast : (((ell - 1 : ℕ)) : ℝ) = (ell : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ ell := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hsq := sum_sq_range ell
  have hR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  rw [hval, hprod, hcast] at hstep1
  nlinarith [hstep1, hsq, hR]

/-! ### THE HEADLINE: no `(2.123)` constant below `(ell−1)²(2ell−1)/18` can hold. -/

/-- **THE SHARPNESS THEOREM.**  Any constant `K` for which the per-block `(2.123)` inequality holds
on the sharpness witness must satisfy `K ≥ (ell−1)²(2ell−1)/18`, which is `Θ(ell³)`.  In particular
the `O(ell²)` sharpening named as the repair route in `Lemma24GeneralEll`'s docstring **does not
exist**, and Bałaban's power `L^d` in `dL^d` is correct in order. -/
theorem block_poincare_constant_lower_bound {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1)) (hstrict : ∀ ν : Fin 3, ell < L ν + 1)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (K : ℝ)
    (h : ∑ b ∈ bondsInBlock y ell, (sw ell b) ^ 2
          ≤ K * ∑ p ∈ plaqsInBlock y ell, (curlValue (sw ell) p) ^ 2) :
    ((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1) / 18 ≤ K := by
  have hR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hlhs := sw_lhs_ge (L := L) hell hdvd hy
  have hrhs := sw_rhs_le (L := L) hdvd hstrict hy
  have hPnn : (0 : ℝ) ≤ ∑ p ∈ plaqsInBlock y ell, (curlValue (sw (L := L) ell) p) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- `K` cannot be negative: the left side is strictly positive
  have hpos : (0 : ℝ) < (2 / 3 : ℝ) * (ell : ℝ) ^ 2 * ((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1) := by
    have h1 : (0 : ℝ) < (ell : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < 2 * (ell : ℝ) - 1 := by linarith
    positivity
  have hK : (0 : ℝ) ≤ K := by
    by_contra hc
    rw [not_le] at hc
    nlinarith [hlhs, h, hPnn, hpos, mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) hPnn]
  have hKr : K * ∑ p ∈ plaqsInBlock y ell, (curlValue (sw (L := L) ell) p) ^ 2
      ≤ K * (12 * (ell : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hrhs hK
  have hchain : (2 / 3 : ℝ) * (ell : ℝ) ^ 2 * ((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1)
      ≤ K * (12 * (ell : ℝ) ^ 2) := le_trans hlhs (le_trans h hKr)
  have hell2pos : (0 : ℝ) < (ell : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 18)]
  nlinarith [hchain, hell2pos]

/-- **The lower bound divided by `ell²` grows without bound** — the quantitative form of "no
`O(ell²)` constant exists": it is at least `ell/18 − 1`. -/
theorem lower_bound_over_sq_grows (ell : ℕ) (hell : 2 ≤ ell) :
    (ell : ℝ) / 18 - 1
      ≤ (((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1) / 18) / (ell : ℝ) ^ 2 := by
  have hR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hpos : (0 : ℝ) < (ell : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith [hR, sq_nonneg ((ell : ℝ) - 2), pow_pos (lt_of_lt_of_le zero_lt_two hR) 3]

/-- **`ell = 21` is a concrete `ell` where the sharpness bound EXCEEDS what the printed exponent
demands**, so the printed `(2.128)` exponent `ell^{-4}` is unreachable through Bałaban's assembly
there: `(20)²·41/18 = 16400/18 = 911.1… > 2·21² = 882 > (108·21⁴ − 6·21²)/(54·21² + 1)`. -/
theorem printed_exponent_blocked_ell21 :
    (108 * (21 : ℝ) ^ 4 - 6 * (21 : ℝ) ^ 2) / (54 * (21 : ℝ) ^ 2 + 1)
      < ((21 : ℝ) - 1) ^ 2 * (2 * (21 : ℝ) - 1) / 18 := by
  norm_num

/-- **THE DECISIVE FORM: no `(2.123)` constant below `(ell−1)²(2ell−1)/18` exists at all.**  Same
statement quantified over EVERY admissible `B`, so it applies to any claimed `(2.123)`.  The
witness's admissibility (`sw_mem`) is load-bearing here: remove it and there is no instantiation.

**SCOPE, added 2026-07-27 after the blind Sol + Kimi gates (both CONFIRMED the obstruction, and Kimi
raised this qualification unprompted).** The hypothesis `h` is the PER-BLOCK inequality at a fixed
coarse `y`, so what is obstructed is any per-block `(2.123)` constant. A hypothetical route that used
only the region-SUMMED inequality (`inBlockBondEnergy ≤ K · inBlockCurlEnergy`, summed over
`y ∈ CoarseLattice`) and never named a per-block constant is **not formally excluded by this
theorem**. That is not a hole in the proof — `(2.123)` is itself per-block, and the `O(L²)` repair
route named in `Lemma24GeneralEll`'s docstring is a per-block sharpening, so the obstruction does hit
its named target. It is a limit on how widely the words "`O(L²)` is impossible" may be repeated:
they are true of the per-block constant, and the region-summed variant is untested rather than
refuted. If anyone wants that variant closed, it is a separate theorem and possibly a real opening. -/
theorem no_subcubic_block_poincare {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1)) (hstrict : ∀ ν : Fin 3, ell < L ν + 1)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (K : ℝ)
    (h : ∀ B ∈ admissibleSubspaceInter L ell,
          ∑ b ∈ bondsInBlock y ell, (B b) ^ 2
            ≤ K * ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2) :
    ((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1) / 18 ≤ K :=
  block_poincare_constant_lower_bound hell hdvd hstrict hy K (h _ (sw_mem ell))

/-- **THE SANDWICH — how far from optimal `block_poincare_sharp` is.**  The proved constant
`(ell+1)(ell−1)²` is at most `18×` the proved lower bound `(ell−1)²(2ell−1)/18`, for every
`ell ≥ 2`.  (The numerically-computed exact optimum is `≈ ell³/3`, i.e. `≈ 3×` below the proved
upper constant — see `compute/block_poincare_sharp/sharp_const.log`; that number is NOT asserted
here, only the kernel-checked factor `18`.) -/
theorem sharp_within_factor_18 (ell : ℕ) (hell : 2 ≤ ell) :
    blockPoincareSharpConst ell
      ≤ 18 * (((ell : ℝ) - 1) ^ 2 * (2 * (ell : ℝ) - 1) / 18) := by
  have hR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  unfold blockPoincareSharpConst
  nlinarith [hR, sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) - 2),
    mul_nonneg (sq_nonneg ((ell : ℝ) - 1)) (sub_nonneg.mpr hR)]

#print axioms no_subcubic_block_poincare
#print axioms sharp_within_factor_18
/-- **THE COMBINED CLASS-(i) STATEMENT.**  At `ell = 21`, whatever constant `C` satisfies the
per-block `(2.123)` inequality, Bałaban's assembly coefficient `bcoef 21 C` STRICTLY EXCEEDS
`108·21⁴` — so the printed `(2.128)` exponent `ell^{-4}` (constant `1/108`) is unreachable through
that assembly at `ell = 21`, for EVERY possible `(2.123)` constant.  Exact rationals:
`no_subcubic_block_poincare` forces `C ≥ 20²·41/18 = 8200/9`, while `needed_2123_constant` requires
`C ≤ (108·21⁴ − 6·21²)/(54·21² + 1) = 21001302/23815`, and `8200/9 > 21001302/23815`. -/
theorem printed_exponent_unreachable_ell21
    (hstrict : ∀ ν : Fin 3, (21 : ℕ) < L ν + 1) (hdvd : ∀ ν : Fin 3, (21 : ℕ) ∣ (L ν + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L 21) (C : ℝ)
    (hC : ∀ B ∈ admissibleSubspaceInter L 21,
          ∑ b ∈ bondsInBlock y 21, (B b) ^ 2
            ≤ C * ∑ p ∈ plaqsInBlock y 21, (curlValue B p) ^ 2) :
    108 * (((21 : ℕ) : ℝ)) ^ 4 < bcoef 21 C := by
  have hlow := no_subcubic_block_poincare (L := L) (ell := 21) (by norm_num) hdvd hstrict hy C hC
  have hb : bcoef 21 C = 2646 + 23815 * C := by unfold bcoef; norm_num
  rw [hb]
  norm_num at hlow ⊢
  linarith [hlow]

#print axioms printed_exponent_unreachable_ell21

#print axioms axialPlaqs_card
#print axioms sw_rhs_le
#print axioms sum_sq_range
#print axioms blkSite_val
#print axioms blkBond_mem
#print axioms sw_blkBond_sq
#print axioms sw_lhs_ge
#print axioms block_poincare_constant_lower_bound
#print axioms lower_bound_over_sq_grows
#print axioms printed_exponent_blocked_ell21

end Sharpness

end AdalyFormal.Balaban.BlockPoincareSharp
