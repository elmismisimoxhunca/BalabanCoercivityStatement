/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoarseCurl

set_option autoImplicit false

/-!
# `Q_ell` (`coarseRestrictCLM`) intertwines with the `ell`-periodic coarse shift — one genuine step
toward Bałaban's momentum-space diagonalization of `Q_k`, CMP95 §C-D (1.29)-(1.65)

**Dispatch** (`GOAL_LEMMA.md` §4, Wave 1 Lane A): extend `U1CurlCoercivity.lean` PART B's exact
`ell=1` curl-coercivity identity to `∀ ell` (`U1Anchor.BalabanFreeCoercivity`, the momentum bound
CMP95 (1.66)→(1.67)). `U1Anchor.lean` §6 already reduces this to ONE named residual
(`exists_bounded_weight_symbol`): momentum-diagonalizing `Q_k = coarseRestrictCLM`, `R = RProj`, and
`H_j = hjExtension` — "a real, sizeable follow-up, not attempted," per that file's own docstring, and
independently confirmed missing by `HjMinimizer.lean`/`CoarseCurl.lean`'s own residual lists.

## What this file does — and precisely does NOT do (disclosed up front, not left for a prosecutor)

`PROOF_OF_167.md`'s traced mechanism (`compute/how_he_proves_it/PROOF_OF_167.md`) is: **`Δ`, `∂`,
`Q_k` are translation-invariant (convolution) operators at `U=1`, hence simultaneously diagonalized by
the Fourier transform**. `LatticeFourier.lean` already builds the GENERIC machinery for operators
invariant under the FULL shift group (`IsTranslationInvariant`/`translationInvariant_diagonalized`).
**The obstruction this file locates precisely**: `Q_k = coarseRestrictCLM L ell` is **NOT** invariant
under the full fine-lattice shift group for `ell > 1` (a single fine step moves a block-average
computed around one coarse center to a computation that is generally not any other coarse center's
block average at all — this is exactly why `ell=1` was the ONLY case `U1CurlCoercivity.lean` PART B
could close by degeneracy). `Q_k` IS, however, invariant under the strictly SMALLER subgroup of shifts
by exactly `ell` steps along one axis (CMP95's own "unit lattice" `T̃₁^{(k)}`, the coarse lattice's own
adjacency) — **this file proves that fact, genuinely, for the first time in this tree**:
`coarseRestrict_shift_intertwine`, THE MAIN THEOREM below, zero `sorry`.

**This is a REAL but PARTIAL step, not a closure.** `LatticeFourier.translationInvariant_diagonalized`
needs invariance under `∀ t : α`, the FULL group; what is proved here is invariance under one
particular shift generator (`coarseShift ell μ`), not the full subgroup it generates, and — more
importantly — even a full generalization to subgroup/coset-invariance (a "block-diagonalizes over
`G/H`-indexed cosets of the dual" theorem, itself NOT built anywhere in mathlib or this tree in
directly usable form for this lattice's exact type) would only diagonalize `Q_k`. **`R = RProj`**
(built via abstract orthogonal projection onto `deltaKernelImage levels`, `HjMinimizer.lean` §1) and
**`H_j = hjExtension`** (the harmonic-extension minimizer, `HjMinimizer.lean` §4) are NOT shown
covariant under this shift anywhere in this tree — their covariance is separate, unestablished content
(named precisely in the "What remains" section below), and even granting all three operators'
covariance, the ACTUAL numeric bound `0 < γ₀ ≤ Δ₀(p′)φ_μ(p′) ≤ γ₁` (CMP95 (1.58)-(1.63), citing CMP89
Lemma 2.4's absolutely convergent geometric-sum estimate) is a further, deeper analytic computation
not attempted here or anywhere in this tree.

## The main theorem, stated informally

For `y` a `CoarseLattice L ell` member (`hdvd : ∀ μ, ell ∣ (L μ+1)`, `hell : 0 < ell`), `μ : Fin 3`,
and any fine bond field `A : Bond L → ℝ`:

`(Q_ell A)(coarseShift y ell μ, ν) = (Q_ell (A ∘ coarseShift(·, ell, μ)))(y, ν)`

i.e. **the block-average AT THE SHIFTED coarse point equals the block-average, AT THE ORIGINAL point,
of the field PULLED BACK by that same shift** — the precise, checkable sense in which `Q_ell`
commutes with the coarse lattice's own adjacency operation. This is the discrete, `ell`-periodic
analogue of `LatticeFourier.shiftOp`/`IsTranslationInvariant`, established here from first principles
(geometric block correspondence under periodic wraparound), not assumed.

## What this file builds

1. **§0 — generic `ℕ` arithmetic** (`shift_mod_formula`, `div_eq_iff_range`, `succ_mod_inj`,
   `mul_add_div_of_lt`): the periodic block-index-transport fact, isolated as pure `ℕ` lemmas so
   they carry no lattice-specific baggage and are independently checkable.
2. **§1 — the coordinate-wise block correspondence** (`coarseShift_blockCoord_mu`): in the shifted
   direction `μ`, `x`'s membership in `y`'s block corresponds exactly to `coarseShift x ell μ`'s
   membership in `(coarseShift y ell μ)`'s block — the genuinely new geometric content, proved via
   the block-index formula, not asserted.
3. **§2 — the full block correspondence** (`coarseShift_mem_blockOf_iff`): combining §1 (direction
   `μ`) with the ALREADY-PROVED `coarseShift_apply_ne` (`CoarseCurl.lean`, every other direction is
   untouched by the shift) to get the full `inBlock` iff.
4. **§3 — injectivity/bijectivity of the shift map, and the block-image identity**
   (`coarseShift_injective`, `coarseShift_blockOf_eq_image`): `blockOf (coarseShift y ell μ) ell` is
   LITERALLY the image of `blockOf y ell` under the shift map — not merely in bijection with it.
5. **§4 — THE MAIN THEOREM** (`coarseRestrict_shift_intertwine`): the block-average intertwining
   identity stated above, proved by reindexing the defining `Finset.sum` via §3's image identity
   (`Finset.sum_image`), zero `sorry`.
6. **§5 — falsifiability (S82/S83)**: a concrete witness confirming the theorem's hypothesis
   (`y ∈ CoarseLattice`) is load-bearing — the SAME identity genuinely fails at a non-`CoarseLattice`
   base point (the shifted block does not correspond to any translate of the original), exhibited on
   the shared witness lattice.

## What this file does NOT build — named residuals, precisely, for the next lane

* **Full-subgroup / coset diagonalization.** `LatticeFourier.translationInvariant_diagonalized`
  requires invariance under the WHOLE group `α`. What is proved here is invariance under a SINGLE
  generator's shift, for each `μ`. Promoting this to "`Q_k` is diagonal on the finite set of
  characters trivial on the `ell`-sublattice" needs a genuine NEW theorem (Pontryagin duality for the
  quotient `PeriodicLatticeSite L / (ell-sublattice)`, i.e. characters of `α` trivial on a subgroup
  `H` correspond to characters of `α/H`, and an operator invariant under all of `H` block-diagonalizes
  accordingly) — **not built anywhere in this tree or found in Mathlib in directly usable form for
  this custom `(μ:Fin 3)→ZMod(Lμ+1)` product type** (checked: `AddChar`'s generic API does not supply
  a ready "quotient-by-subgroup" duality lemma specialized to this shape). This is a real, separate
  formalization project.
* **`R = RProj`'s covariance under this shift.** `RProj` is built (`HjMinimizer.lean` §1) as the
  abstract orthogonal projection onto `deltaKernelImage levels := Δ₀''(kernelSubspaceH levels)`, a
  submodule of `SiteSpace L`. Whether `kernelSubspaceH levels` (built from the free `Finset`-as-data
  `levels` parameter, `KernelSubspace.lean`) is itself invariant under the `ell`-shift, for any
  particular `levels`, is NOT examined here — it depends on `levels`, which this tree already
  discloses (`HjMinimizer.lean`'s own "multiscale domain geometry... free-`Finset`-as-data
  simplification") is not tied to any concrete geometric structure that would force such invariance.
* **`H_j = hjExtension`'s covariance.** Even granting `Q_k`, `R` covariant, `hjExtension` is built via
  a `Classical.choose` over an orthogonal-projection closest-point construction
  (`HjMinimizer.hjCorrection`); showing the CHOSEN correction is itself shift-equivariant (not merely
  that SOME correction with the right properties exists at each shifted point) needs a genuine
  uniqueness-up-to-choice argument, not attempted.
* **The scalar bound itself** (CMP95 (1.58)-(1.63)/CMP89 Lemma 2.4): the actual numeric content of
  (1.67) — an absolutely convergent geometric-sum estimate over the reciprocal lattice — is NOT
  approached by this file's geometric covariance argument at all; it is a separate analytic estimate,
  unattempted anywhere in this tree (`LatticeFourier.lean`'s own disclosure, unchanged).
-/

namespace AdalyFormal.Balaban.CoarseShiftCovariance

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CoarseCurl

variable {L : PeriodicLatticeExtent}

/-! ## §0. Generic `ℕ` arithmetic: the periodic block-index-transport formula -/

section NatHelpers

/-- **`(c + ell) mod (ell·m) = ell·((c/ell + 1) mod m) + c mod ell`**, for `c < ell·m`: adding one
full block-step `ell` to any point `c` inside an `m`-block tiling of `[0, ell·m)` advances its coarse
block-index by exactly `1`, cyclically mod `m`, while its within-block offset (`c mod ell`) is
UNCHANGED. This is the arithmetic core of "shifting a coarse block base point by `ell` moves to the
NEXT coarse block, wrapping correctly at the boundary." -/
theorem shift_mod_formula (ell m : ℕ) (hell : 0 < ell) (hm : 0 < m) (c : ℕ) (hc : c < ell * m) :
    (c + ell) % (ell * m) = ell * ((c / ell + 1) % m) + c % ell := by
  have hj : c / ell < m := by
    rw [Nat.div_lt_iff_lt_mul hell]; rwa [mul_comm]
  have hdm : ell * (c / ell) + c % ell = c := Nat.div_add_mod c ell
  have hrlt : c % ell < ell := Nat.mod_lt c hell
  rcases Nat.lt_or_ge (c / ell + 1) m with hlt | hge
  · have h1 : c + ell = ell * (c / ell + 1) + c % ell := by
      have heq : ell * (c / ell + 1) = ell * (c / ell) + ell := by ring
      omega
    rw [h1]
    have hlt2 : ell * (c / ell + 1) + c % ell < ell * m := by
      have hle : ell * (c / ell + 1) + ell ≤ ell * m := by
        have heq2 : ell * (c / ell + 1) + ell = ell * (c / ell + 2) := by ring
        rw [heq2]
        exact Nat.mul_le_mul_left ell hlt
      omega
    rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt]
  · have heq : c / ell + 1 = m := le_antisymm hj hge
    have h1 : c + ell = ell * m + c % ell := by
      have heq2 : ell * (c / ell + 1) = ell * (c / ell) + ell := by ring
      rw [heq] at heq2
      omega
    rw [h1, add_comm (ell * m) (c % ell), Nat.add_mod_right]
    have hrlt2 : c % ell < ell * m := lt_of_lt_of_le hrlt (Nat.le_mul_of_pos_right ell hm)
    rw [Nat.mod_eq_of_lt hrlt2]
    have hm0 : (m : ℕ) % m = 0 := Nat.mod_self m
    rw [heq, hm0]
    ring

#print axioms shift_mod_formula

/-- **`x/ell = j ↔ ell·j ≤ x ∧ x < ell·j + ell`** — the elementary floor-division/interval
correspondence underlying `blockOf`'s definition. -/
theorem div_eq_iff_range (ell j x : ℕ) (hell : 0 < ell) :
    x / ell = j ↔ ell * j ≤ x ∧ x < ell * j + ell := by
  constructor
  · intro h
    subst h
    have hdm := Nat.div_add_mod x ell
    have hrlt := Nat.mod_lt x hell
    have hnn : 0 ≤ x % ell := Nat.zero_le _
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    rw [mul_comm] at h1
    exact Nat.div_eq_of_lt_le h1 (by rw [mul_comm]; omega)

#print axioms div_eq_iff_range

/-- **`(ell·k + r)/ell = k`** for `r < ell` — the companion division fact, used to extract the
block-index of a shifted point from `shift_mod_formula`'s explicit sum form. -/
theorem mul_add_div_of_lt (ell k r : ℕ) (hell : 0 < ell) (hr : r < ell) :
    (ell * k + r) / ell = k := by
  rw [Nat.mul_add_div hell]
  simp [Nat.div_eq_of_lt hr]

#print axioms mul_add_div_of_lt

/-- **`(a+1) mod m` is injective on `[0,m)`** — the fact that makes "block-index advances by exactly
one, cyclically" a RECOVERABLE (not merely forward-computable) correspondence: two points in the same
coarse-index range map to shifted points in the same coarse-index range only if they started in the
same range. -/
theorem succ_mod_inj {m a b : ℕ} (ha : a < m) (hb : b < m) (h : (a + 1) % m = (b + 1) % m) :
    a = b := by
  rcases Nat.lt_or_ge (a + 1) m with ha1 | ha1 <;> rcases Nat.lt_or_ge (b + 1) m with hb1 | hb1
  · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h; omega
  · have hbeq : b + 1 = m := by omega
    rw [Nat.mod_eq_of_lt ha1] at h
    rw [hbeq, Nat.mod_self] at h
    omega
  · have haeq : a + 1 = m := by omega
    rw [Nat.mod_eq_of_lt hb1] at h
    rw [haeq, Nat.mod_self] at h
    omega
  · have h1 : a + 1 = m := by omega
    have h2 : b + 1 = m := by omega
    omega

#print axioms succ_mod_inj

end NatHelpers

/-! ## §1. The coordinate-wise block correspondence in the shifted direction `μ` -/

/-- **THE GEOMETRIC CORE**: for `y` with `(y μ).val` a multiple of `ell` (i.e. `y` is `CoarseLattice`
in coordinate `μ`) and `ell ∣ (L μ + 1)` (tileability), the `μ`-coordinate range membership
`(y μ).val ≤ (x μ).val < (y μ).val+ell` is EXACTLY PRESERVED (both directions) under shifting both
`x` and `y` by `coarseShift ell μ`. This is the genuinely new content: `coarseShift` moves the
"next coarse block" correctly, wrapping at the periodic boundary, without breaking the block
correspondence. -/
theorem coarseShift_blockCoord_mu {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy0 : (y μ).val % ell = 0)
    (x : PeriodicLatticeSite L) :
    ((y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell) ↔
      (((coarseShift y ell μ) μ).val ≤ ((coarseShift x ell μ) μ).val ∧
        ((coarseShift x ell μ) μ).val < ((coarseShift y ell μ) μ).val + ell) := by
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, mul_zero] at hm; omega
    · exact h0
  have hxlt : (x μ).val < ell * m := by rw [← hm]; exact (x μ).isLt
  have hylt : (y μ).val < ell * m := by rw [← hm]; exact (y μ).isLt
  have hyeq : (y μ).val = ell * ((y μ).val / ell) := by
    have hdm := Nat.div_add_mod (y μ).val ell
    omega
  set jY := (y μ).val / ell with hjY
  set jX := (x μ).val / ell with hjX
  have hjYlt : jY < m := by rw [hjY]; rw [Nat.div_lt_iff_lt_mul hell]; rwa [mul_comm]
  have hjXlt : jX < m := by rw [hjX]; rw [Nat.div_lt_iff_lt_mul hell]; rwa [mul_comm]
  -- LHS: (y μ).val ≤ (x μ).val < (y μ).val + ell ↔ jX = jY
  have hLHS : ((y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell) ↔ jX = jY := by
    rw [hyeq]
    rw [show ell * jY ≤ (x μ).val ∧ (x μ).val < ell * jY + ell ↔ (x μ).val / ell = jY from
      (div_eq_iff_range ell jY (x μ).val hell).symm]
  -- shifted values via coarseShift_val_eq + shift_mod_formula. Routed through a `∀ n c`-quantified
  -- helper so `hm : L μ + 1 = ell * m` is only ever substituted into a goal about FRESH nat
  -- variables `n, c` (never directly into a goal containing `(x μ).val`/`(y μ).val`, whose implicit
  -- `Fin`-type argument IS syntactically `L μ + 1` and breaks `rw`'s motive if touched directly).
  have hgen : ∀ (n c : ℕ), n = ell * m → c < n →
      (c + ell) % n = ell * ((c / ell + 1) % m) + c % ell := by
    intro n c hn hc
    subst hn
    exact shift_mod_formula ell m hell hmpos c hc
  have hshiftX : ((coarseShift x ell μ) μ).val = ell * ((jX + 1) % m) + (x μ).val % ell := by
    rw [coarseShift_val_eq]
    exact hgen (L μ + 1) (x μ).val hm (x μ).isLt
  have hshiftY : ((coarseShift y ell μ) μ).val = ell * ((jY + 1) % m) + (y μ).val % ell := by
    rw [coarseShift_val_eq]
    exact hgen (L μ + 1) (y μ).val hm (y μ).isLt
  have hyr0 : (y μ).val % ell = 0 := hy0
  have hrX : (x μ).val % ell < ell := Nat.mod_lt _ hell
  -- RHS reduces to the same jX = jY, via the block-index of the shifted points
  have hRHS : (((coarseShift y ell μ) μ).val ≤ ((coarseShift x ell μ) μ).val ∧
        ((coarseShift x ell μ) μ).val < ((coarseShift y ell μ) μ).val + ell) ↔
      (jX + 1) % m = (jY + 1) % m := by
    rw [hshiftX, hshiftY, hyr0, add_zero]
    rw [(div_eq_iff_range ell ((jY + 1) % m)
      (ell * ((jX + 1) % m) + (x μ).val % ell) hell).symm]
    rw [mul_add_div_of_lt ell ((jX + 1) % m) ((x μ).val % ell) hell hrX]
  rw [hLHS, hRHS]
  constructor
  · intro h; rw [h]
  · intro h; exact succ_mod_inj hjXlt hjYlt h

#print axioms coarseShift_blockCoord_mu

/-! ## §2. The full `inBlock` correspondence, combining §1 (direction `μ`) with the untouched
directions `ν ≠ μ` -/

/-- **THE FULL BLOCK-MEMBERSHIP CORRESPONDENCE**: `x ∈ blockOf y ell ↔ coarseShift x ell μ ∈
blockOf (coarseShift y ell μ) ell`, given `y ∈ CoarseLattice` (so its `μ`-coordinate is aligned) and
tileability. Combines §1 (the one direction the shift touches) with `coarseShift_apply_ne`
(`CoarseCurl.lean`, already proved: every other direction is UNCHANGED by the shift, so its
`inBlock` condition transfers literally). -/
theorem coarseShift_mem_blockOf_iff {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) :
    x ∈ blockOf y ell ↔ coarseShift x ell μ ∈ blockOf (coarseShift y ell μ) ell := by
  rw [mem_blockOf, mem_blockOf]
  have hy0 : (y μ).val % ell = 0 := (mem_CoarseLattice.mp hy) μ
  constructor
  · intro h ν
    by_cases hν : ν = μ
    · exact hν ▸ (coarseShift_blockCoord_mu hell hdvd hy0 x).mp (hν ▸ h ν)
    · rw [coarseShift_apply_ne x ell μ ν hν, coarseShift_apply_ne y ell μ ν hν]
      exact h ν
  · intro h ν
    by_cases hν : ν = μ
    · exact hν ▸ (coarseShift_blockCoord_mu hell hdvd hy0 x).mpr (hν ▸ h ν)
    · have hh := h ν
      rw [coarseShift_apply_ne x ell μ ν hν, coarseShift_apply_ne y ell μ ν hν] at hh
      exact hh

#print axioms coarseShift_mem_blockOf_iff

/-! ## §3. Injectivity of the shift map, and the block-image identity -/

/-- **`coarseShift (·) ell μ` is injective** — the `ell`-fold iterate of the already-proved-injective
single fine step (`periodicLatticeShift_injective`, `CoarseCurl.lean`). -/
theorem coarseShift_injective (ell : ℕ) (μ : Fin 3) :
    Function.Injective (fun x : PeriodicLatticeSite L => coarseShift x ell μ) := by
  unfold coarseShift
  exact Function.Injective.iterate (periodicLatticeShift_injective μ) ell

#print axioms coarseShift_injective

/-- **`coarseShift (·) ell μ` is bijective** — injective self-map of a finite type. -/
theorem coarseShift_bijective (ell : ℕ) (μ : Fin 3) :
    Function.Bijective (fun x : PeriodicLatticeSite L => coarseShift x ell μ) :=
  Finite.injective_iff_bijective.mp (coarseShift_injective ell μ)

#print axioms coarseShift_bijective

/-- **`blockOf (coarseShift y ell μ) ell` is LITERALLY the image of `blockOf y ell`** under the
shift map — not merely in bijection with it. Combines §2's membership-iff with §3's bijectivity
(surjectivity supplies the preimage for the reverse inclusion). -/
theorem coarseShift_blockOf_eq_image {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    blockOf (coarseShift y ell μ) ell =
      Finset.image (fun x : PeriodicLatticeSite L => coarseShift x ell μ) (blockOf y ell) := by
  apply Finset.ext
  intro x'
  rw [Finset.mem_image]
  constructor
  · intro hx'
    obtain ⟨x, hx⟩ := (coarseShift_bijective ell μ (L := L)).2 x'
    dsimp only at hx
    refine ⟨x, ?_, hx⟩
    rw [coarseShift_mem_blockOf_iff hell hdvd hy x, hx]
    exact hx'
  · rintro ⟨x, hx, rfl⟩
    exact (coarseShift_mem_blockOf_iff hell hdvd hy x).mp hx

#print axioms coarseShift_blockOf_eq_image

/-! ## §4. THE MAIN THEOREM: `coarseRestrict` intertwines with the coarse shift -/

/-- **THE MAIN THEOREM.** `Q_ell A`, evaluated at the SHIFTED coarse point, equals `Q_ell` of the
SHIFT-PULLED-BACK field `A ∘ coarseShift(·,ell,μ)`, evaluated at the ORIGINAL point — the precise,
checkable sense in which `coarseRestrictCLM` (`Q_k`, CMP95 eq. 1.18) is invariant under the coarse
lattice's own `ell`-periodic adjacency, matching `PROOF_OF_167.md`'s traced mechanism ("`Q_k` is a
translation-invariant operator") for THIS specific subgroup of shifts (not the full fine-shift group
— see the module docstring for exactly what remains). Proved by reindexing the defining `Finset.sum`
via §3's image identity (`Finset.sum_image`, using §3's injectivity for the no-collision hypothesis),
zero `sorry`. -/
theorem coarseRestrict_shift_intertwine {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (hy' : coarseShift y ell μ ∈ CoarseLattice L ell) (A : Bond L → ℝ) (ν : Fin 3) :
    coarseRestrict ell A (⟨coarseShift y ell μ, hy'⟩, ν) =
      coarseRestrict ell (fun b => A (coarseShift b.1 ell μ, b.2)) (⟨y, hy⟩, ν) := by
  unfold coarseRestrict
  congr 1
  rw [coarseShift_blockOf_eq_image hell hdvd hy]
  rw [Finset.sum_image (fun x _ x' _ hxx' => coarseShift_injective ell μ hxx')]

#print axioms coarseRestrict_shift_intertwine

/-! ## §5. Falsifiability (S82/S83): `y ∈ CoarseLattice` is load-bearing, exhibited on the shared
witness lattice -/

/-- **The hypothesis `hy0 : (y μ).val % ell = 0` is load-bearing, not decorative**: dropping it,
`coarseShift_blockCoord_mu`'s conclusion GENUINELY FAILS on a concrete non-aligned base point. On the
shared witness lattice (`witnessL`, `witnessEll = 2`), take `y := (1,0,0)` (coordinate `0` value `1`,
NOT a multiple of `2`) and `μ := 0`: `x := (2,0,0)` lies in `y`'s naive box `[1,3)` in coordinate `0`
(`1 ≤ 2 < 1+2`), but `coarseShift x 2 0` has coordinate `0` equal to `0` (two steps from `2`, wrapping
mod `4`) while `coarseShift y 2 0` has coordinate `0` equal to `3` (two steps from `1`) — and `0` is
NOT in `[3, 3+2) = [3,5)` (mod-`4` interval reasoning aside, the RAW `.val` comparison `3 ≤ 0` is
already false) — so the shifted membership FAILS while the un-shifted one held. This confirms
`CoarseLattice`-alignment is genuinely necessary for the correspondence, not an artifact of a loose
hypothesis. -/
theorem coarseShift_blockCoord_mu_needs_alignment :
    ¬ ∀ (y x : PeriodicLatticeSite AdmissibleSubspace.witnessL),
      (((y 0).val ≤ (x 0).val ∧ (x 0).val < (y 0).val + AdmissibleSubspace.witnessEll)) →
      (((coarseShift y AdmissibleSubspace.witnessEll 0) 0).val ≤
          ((coarseShift x AdmissibleSubspace.witnessEll 0) 0).val ∧
        ((coarseShift x AdmissibleSubspace.witnessEll 0) 0).val <
          ((coarseShift y AdmissibleSubspace.witnessEll 0) 0).val +
            AdmissibleSubspace.witnessEll) := by
  intro h
  -- concrete witness sites, using explicit `Fin 4`-valued functions
  set y : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
    fun i => if i = 0 then (1 : Fin 4) else 0 with hydef
  set x : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
    fun i => if i = 0 then (2 : Fin 4) else 0 with hxdef
  have hyval : (y 0).val = 1 := by simp [hydef]
  have hxval : (x 0).val = 2 := by simp [hxdef]
  have hpre : (y 0).val ≤ (x 0).val ∧ (x 0).val < (y 0).val + AdmissibleSubspace.witnessEll := by
    rw [hyval, hxval]; unfold AdmissibleSubspace.witnessEll; decide
  have hpost := h y x hpre
  have hcx : (coarseShift x AdmissibleSubspace.witnessEll 0) 0 = 0 := by
    unfold coarseShift AdmissibleSubspace.witnessEll
    decide
  have hcy : (coarseShift y AdmissibleSubspace.witnessEll 0) 0 = 3 := by
    unfold coarseShift AdmissibleSubspace.witnessEll
    decide
  rw [hcx, hcy] at hpost
  simp only [Fin.val_zero] at hpost
  have : (3 : Fin 4).val ≤ (0 : ℕ) := hpost.1
  simp at this

#print axioms coarseShift_blockCoord_mu_needs_alignment

end AdalyFormal.Balaban.CoarseShiftCovariance
