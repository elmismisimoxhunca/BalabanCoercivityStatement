/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LineIntegralAveraging

set_option autoImplicit false

/-!
# The discrete Poincaré / Hodge lemma on the periodic 3-torus — `∂₁A = 0 ⟹ A = ∂₀f + c`

**What this file proves** (`curlFree_eq_grad_add_const`, zero `sorry`): on ANY
`PeriodicLatticeExtent Λ`, a bond field with identically vanishing curl is the sum of a gradient
and a DIRECTION-CONSTANT field:

  `(∀ p, curlValue A p = 0) → ∃ f c, ∀ b, A b = f (shift b.1 b.2) - f b.1 + c b.2`.

**Why this object and not the naive Poincaré lemma.** On a torus `H¹ ≠ 0`: the three constants
`c μ` are the harmonic classes and they CANNOT be dropped — `curlFree_of_grad_add_const` proves a
constant field is curl-free, and `const_not_gradValue` exhibits a curl-free field that is NOT a
gradient (so the `c` is load-bearing, not decoration). This is exactly the point
`U1Anchor.lean` §8's `(P1)` names: *"On a 3-torus this is not the naive Poincaré lemma — the
constant/harmonic classes are real and must be carried, which is exactly where a careless proof
would go wrong."*

**Where it is consumed**: `U1AnchorCoarse.lean` transports it to the COARSE lattice
(`CoarseCurl.coarseCurlValue`), which is what `U1Anchor.exists_bounded_weight_symbol` needs.

**The proof is the axial-gauge algorithm run three times**, not the 3-fold staircase:

1. `transport` — curl-freeness, restated as `A(x+e_ν,μ) − A(x,μ) = A(x+e_μ,ν) − A(x,ν)`, valid for
   ALL `μ,ν` (both orderings and the diagonal), so no direction bookkeeping downstream.
2. `lineIntegralValue_shift` — the master identity: the `k`-step line integral in direction `ν`
   changes, under one step in direction `μ`, by exactly `A(x+k·e_ν,μ) − A(x,μ)`. Proof: induct on
   `k`, telescoping through `transport`.
3. `holonomy_const` — at `k = Λ ν + 1` the endpoint returns (`coarseShift_period`), so the full
   cycle integral is shift-invariant in EVERY direction, hence constant (the shifts act
   transitively, `eq_of_shiftInvariant`). Its value over the cycle length is the constant `c ν`.
4. `potential_grad` — with the holonomies removed, the partial line integral from the
   `ν`-coordinate-zeroed base point is a genuine potential for the `ν`-component; the wraparound
   branch is exactly where the vanishing holonomy is spent.
5. `gauge_step` packages one axial-gauge sweep TOGETHER with the invariance bookkeeping
   (`already-gauged components stay gauged`) that stops later sweeps undoing earlier ones; §7
   applies it three times.

Every object is REUSED (LAW-19): `periodicLatticeShift`, `curlValue`, `gradValue`
(`LatticeOperators`), `coarseShift` (`CoarseCurl`, the `k`-fold shift iterate), `lineIntegralValue`
(`LineIntegralAveraging`, CMP95 (1.8)). Nothing here is re-defined.
-/

namespace AdalyFormal.Balaban.U1AnchorPoincare

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging

variable {Λ : PeriodicLatticeExtent}

/-! ## §1. Shift algebra: iteration, commutation, period, transitivity -/

theorem shift_apply_ne (x : PeriodicLatticeSite Λ) (μ ν : Fin 3) (h : ν ≠ μ) :
    periodicLatticeShift x μ ν = x ν :=
  Function.update_of_ne h _ _

theorem coarseShift_zero (x : PeriodicLatticeSite Λ) (μ : Fin 3) : coarseShift x 0 μ = x := rfl

theorem coarseShift_one (x : PeriodicLatticeSite Λ) (μ : Fin 3) :
    coarseShift x 1 μ = periodicLatticeShift x μ := rfl

theorem coarseShift_succ (x : PeriodicLatticeSite Λ) (k : ℕ) (μ : Fin 3) :
    coarseShift x (k + 1) μ = periodicLatticeShift (coarseShift x k μ) μ :=
  Function.iterate_succ_apply' _ _ _

/-- The two coordinate shifts commute — including the DIAGONAL case `μ = ν`, where they are the
same function. Stating it for all pairs removes every `μ ≠ ν` side condition below. -/
theorem shift_commute (μ ν : Fin 3) :
    Function.Commute (fun z : PeriodicLatticeSite Λ => periodicLatticeShift z μ)
      (fun z => periodicLatticeShift z ν) := by
  by_cases h : μ = ν
  · subst h; exact Function.Commute.refl _
  · intro z; exact (periodicLatticeShift_comm z h).symm

theorem coarseShift_comm_gen (x : PeriodicLatticeSite Λ) (k m : ℕ) (μ ν : Fin 3) :
    coarseShift (coarseShift x k μ) m ν = coarseShift (coarseShift x m ν) k μ :=
  (((shift_commute (Λ := Λ) ν μ).iterate_left m).iterate_right k) x

/-- One step in direction `μ` commutes with `k` steps in direction `ν`. -/
theorem shift_coarseShift (x : PeriodicLatticeSite Λ) (k : ℕ) (μ ν : Fin 3) :
    coarseShift (periodicLatticeShift x μ) k ν =
      periodicLatticeShift (coarseShift x k ν) μ := by
  have h := coarseShift_comm_gen x 1 k μ ν
  rwa [coarseShift_one, coarseShift_one] at h

/-- The `μ`-coordinate after one step. -/
theorem shift_val (x : PeriodicLatticeSite Λ) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (Λ μ + 1) := by
  rw [← coarseShift_one]
  exact coarseShift_val_eq x 1 μ

/-- **The period**: `Λ μ + 1` steps in direction `μ` return to the starting site. -/
theorem coarseShift_period (x : PeriodicLatticeSite Λ) (μ : Fin 3) :
    coarseShift x (Λ μ + 1) μ = x := by
  funext ν
  by_cases h : ν = μ
  · subst h
    apply Fin.ext
    rw [coarseShift_val_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (x ν).isLt]
  · exact coarseShift_apply_ne x (Λ μ + 1) μ ν h

/-- Two sites agreeing off direction `μ` are connected by `μ`-shifts. -/
theorem exists_coarseShift_of_agree (x y : PeriodicLatticeSite Λ) (μ : Fin 3)
    (h : ∀ ν, ν ≠ μ → x ν = y ν) : ∃ k : ℕ, coarseShift x k μ = y := by
  refine ⟨(y μ).val + (Λ μ + 1) - (x μ).val, ?_⟩
  funext ν
  by_cases hν : ν = μ
  · subst hν
    apply Fin.ext
    rw [coarseShift_val_eq]
    have h1 := (x ν).isLt
    have h2 := (y ν).isLt
    have he : (x ν).val + ((y ν).val + (Λ ν + 1) - (x ν).val) = (y ν).val + (Λ ν + 1) := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
  · rw [coarseShift_apply_ne _ _ _ _ hν]
    exact h ν hν

/-- A function invariant under every one-step shift is constant: the shifts act transitively. -/
theorem eq_of_shiftInvariant {α : Type*} (g : PeriodicLatticeSite Λ → α)
    (hg : ∀ (x : PeriodicLatticeSite Λ) (μ : Fin 3), g (periodicLatticeShift x μ) = g x)
    (x y : PeriodicLatticeSite Λ) : g x = g y := by
  classical
  have hiter : ∀ (z : PeriodicLatticeSite Λ) (μ : Fin 3) (k : ℕ), g (coarseShift z k μ) = g z := by
    intro z μ k
    induction k with
    | zero => rfl
    | succ n ih => rw [coarseShift_succ, hg, ih]
  have hupd : ∀ (z : PeriodicLatticeSite Λ) (μ : Fin 3) (v : Fin (Λ μ + 1)),
      g (Function.update z μ v) = g z := by
    intro z μ v
    obtain ⟨k, hk⟩ := exists_coarseShift_of_agree z (Function.update z μ v) μ
      (fun ν hν => (Function.update_of_ne hν _ _).symm)
    rw [← hk]
    exact hiter z μ k
  have h3 : Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (y 2) = y := by
    funext ν
    by_cases h2 : ν = 2
    · subst h2; rw [Function.update_self]
    · rw [Function.update_of_ne h2]
      by_cases h1 : ν = 1
      · subst h1; rw [Function.update_self]
      · rw [Function.update_of_ne h1]
        have h0 : ν = 0 := by
          have hlt := ν.isLt
          have e1 : ν.val ≠ 1 := fun hc => h1 (Fin.ext hc)
          have e2 : ν.val ≠ 2 := fun hc => h2 (Fin.ext hc)
          apply Fin.ext
          omega
        subst h0
        rw [Function.update_self]
  calc g x = g (Function.update x 0 (y 0)) := (hupd _ _ _).symm
    _ = g (Function.update (Function.update x 0 (y 0)) 1 (y 1)) := (hupd _ _ _).symm
    _ = g (Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (y 2)) :=
        (hupd _ _ _).symm
    _ = g y := by rw [h3]

/-! ## §2. Curl-freeness and the transport identity -/

/-- `∂₁A = 0`, stated pointwise on `curlValue` (`LatticeOperators`, CMP95 (1.2)). -/
def CurlFree (A : Bond Λ → ℝ) : Prop := ∀ p : PeriodicLatticePlaquette Λ, curlValue A p = 0

/-- **TRANSPORT.** Curl-freeness says the `μ`-component's increment across one `ν`-step equals the
`ν`-component's increment across one `μ`-step — for EVERY ordered pair, including `μ = ν`. -/
theorem transport {A : Bond Λ → ℝ} (hA : CurlFree A) (x : PeriodicLatticeSite Λ) (μ ν : Fin 3) :
    A (periodicLatticeShift x ν, μ) - A (x, μ) =
      A (periodicLatticeShift x μ, ν) - A (x, ν) := by
  rcases lt_trichotomy μ ν with h | h | h
  · have hc := hA (x, ⟨(μ, ν), h⟩)
    simp only [curlValue] at hc
    linarith
  · subst h; rfl
  · have hc := hA (x, ⟨(ν, μ), h⟩)
    simp only [curlValue] at hc
    linarith

theorem curlValue_sub (F G : Bond Λ → ℝ) (p : PeriodicLatticePlaquette Λ) :
    curlValue (fun b => F b - G b) p = curlValue F p - curlValue G p := by
  simp only [curlValue]; ring

/-- Constant-per-direction fields are curl-free (the harmonic classes of the torus). -/
theorem curlValue_of_const (c : Fin 3 → ℝ) (p : PeriodicLatticePlaquette Λ) :
    curlValue (fun b : Bond Λ => c b.2) p = 0 := by
  simp only [curlValue]; ring

/-! ## §3. The master identity for the line integral -/

theorem lineIntegralValue_zero (A : Bond Λ → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    lineIntegralValue 0 A x ν = 0 := by
  simp [lineIntegralValue]

theorem lineIntegralValue_succ (k : ℕ) (A : Bond Λ → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    lineIntegralValue (k + 1) A x ν =
      lineIntegralValue k A x ν + A (coarseShift x k ν, ν) :=
  Finset.sum_range_succ _ _

theorem lineIntegralValue_sub (k : ℕ) (F G : Bond Λ → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    lineIntegralValue k (fun b => F b - G b) x ν =
      lineIntegralValue k F x ν - lineIntegralValue k G x ν := by
  simp only [lineIntegralValue]
  rw [← Finset.sum_sub_distrib]

theorem lineIntegralValue_const (k : ℕ) (c : Fin 3 → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    lineIntegralValue k (fun b : Bond Λ => c b.2) x ν = (k : ℝ) * c ν := by
  simp only [lineIntegralValue, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **THE MASTER IDENTITY.** Under one step in direction `μ`, the `k`-step line integral in
direction `ν` changes by exactly the `μ`-component's endpoint difference. Proof: induction on `k`,
telescoping through `transport`. -/
theorem lineIntegralValue_shift {A : Bond Λ → ℝ} (hA : CurlFree A) (x : PeriodicLatticeSite Λ)
    (μ ν : Fin 3) (k : ℕ) :
    lineIntegralValue k A (periodicLatticeShift x μ) ν - lineIntegralValue k A x ν =
      A (coarseShift x k ν, μ) - A (x, μ) := by
  induction k with
  | zero => simp [lineIntegralValue, coarseShift_zero]
  | succ n ih =>
    rw [lineIntegralValue_succ, lineIntegralValue_succ, shift_coarseShift x n μ ν,
      coarseShift_succ]
    have htr := transport hA (coarseShift x n ν) ν μ
    linarith

/-! ## §4. The holonomy is a base-point-independent constant — the harmonic class -/

/-- The full cycle integral of `A` in direction `ν`, based at `x`. -/
noncomputable def holonomy (A : Bond Λ → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) : ℝ :=
  lineIntegralValue (Λ ν + 1) A x ν

theorem holonomy_shift {A : Bond Λ → ℝ} (hA : CurlFree A) (x : PeriodicLatticeSite Λ)
    (μ ν : Fin 3) : holonomy A (periodicLatticeShift x μ) ν = holonomy A x ν := by
  have h := lineIntegralValue_shift hA x μ ν (Λ ν + 1)
  rw [coarseShift_period] at h
  simp only [holonomy]
  linarith

/-- **The holonomy does not depend on the base point** — the discrete statement that a curl-free
field's period around each cycle is a topological invariant. -/
theorem holonomy_const {A : Bond Λ → ℝ} (hA : CurlFree A) (x y : PeriodicLatticeSite Λ)
    (ν : Fin 3) : holonomy A x ν = holonomy A y ν :=
  eq_of_shiftInvariant (fun z => holonomy A z ν) (fun z μ => holonomy_shift hA z μ ν) x y

theorem holonomy_sub (F G : Bond Λ → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    holonomy (fun b => F b - G b) x ν = holonomy F x ν - holonomy G x ν :=
  lineIntegralValue_sub _ _ _ _ _

/-- A gradient has zero holonomy: the telescoping sum closes up around the cycle. -/
theorem holonomy_gradValue (f : PeriodicLatticeSite Λ → ℝ) (x : PeriodicLatticeSite Λ)
    (ν : Fin 3) : holonomy (gradValue f) x ν = 0 := by
  simp only [holonomy]
  rw [lineIntegralValue_gradValue, coarseShift_period]
  ring

theorem holonomy_const_field (c : Fin 3 → ℝ) (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    holonomy (fun b : Bond Λ => c b.2) x ν = ((Λ ν : ℝ) + 1) * c ν := by
  simp only [holonomy]
  rw [lineIntegralValue_const]
  push_cast
  ring

/-! ## §5. The axial-gauge potential -/

/-- The base point of the `ν`-line through `x`: `x` with its `ν`-coordinate set to `0`. -/
def zeroOut (x : PeriodicLatticeSite Λ) (ν : Fin 3) : PeriodicLatticeSite Λ :=
  Function.update x ν 0

theorem zeroOut_apply_self (x : PeriodicLatticeSite Λ) (ν : Fin 3) : zeroOut x ν ν = 0 :=
  Function.update_self _ _ _

theorem zeroOut_apply_ne (x : PeriodicLatticeSite Λ) {ν μ : Fin 3} (h : μ ≠ ν) :
    zeroOut x ν μ = x μ := Function.update_of_ne h _ _

/-- Walking `(x ν).val` steps in direction `ν` from the zeroed base point lands back on `x`. -/
theorem coarseShift_zeroOut (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    coarseShift (zeroOut x ν) ((x ν).val) ν = x := by
  funext μ
  by_cases h : μ = ν
  · subst h
    apply Fin.ext
    rw [coarseShift_val_eq, zeroOut_apply_self]
    simp only [Fin.val_zero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (x μ).isLt
  · rw [coarseShift_apply_ne _ _ _ _ h, zeroOut_apply_ne x h]

theorem zeroOut_shift_self (x : PeriodicLatticeSite Λ) (ν : Fin 3) :
    zeroOut (periodicLatticeShift x ν) ν = zeroOut x ν := by
  funext μ
  by_cases h : μ = ν
  · subst h; rw [zeroOut_apply_self, zeroOut_apply_self]
  · rw [zeroOut_apply_ne _ h, zeroOut_apply_ne _ h, shift_apply_ne x ν μ h]

theorem zeroOut_shift_ne (x : PeriodicLatticeSite Λ) {μ ν : Fin 3} (h : μ ≠ ν) :
    zeroOut (periodicLatticeShift x μ) ν = periodicLatticeShift (zeroOut x ν) μ := by
  funext ρ
  by_cases hρ : ρ = ν
  · subst hρ
    rw [zeroOut_apply_self, shift_apply_ne _ μ ρ (Ne.symm h), zeroOut_apply_self]
  · rw [zeroOut_apply_ne _ hρ]
    by_cases hρμ : ρ = μ
    · subst hρμ
      rw [CoarseCurl.periodicLatticeShift_self, CoarseCurl.periodicLatticeShift_self,
        zeroOut_apply_ne x hρ]
    · rw [shift_apply_ne _ μ ρ hρμ, shift_apply_ne _ μ ρ hρμ, zeroOut_apply_ne x hρ]

/-- **The axial-gauge potential** for direction `ν`: the line integral from the `ν`-zeroed base
point up to `x`. -/
noncomputable def potential (A : Bond Λ → ℝ) (ν : Fin 3) (x : PeriodicLatticeSite Λ) : ℝ :=
  lineIntegralValue ((x ν).val) A (zeroOut x ν) ν

/-- **THE GAUGE STEP.** With the `ν`-holonomies removed, `potential A ν` is a genuine potential for
the `ν`-component of `A`. The wraparound branch is exactly where the vanishing holonomy is spent —
this is the step that is FALSE on a torus without the harmonic correction. -/
theorem potential_grad {A : Bond Λ → ℝ} (ν : Fin 3)
    (hhol : ∀ z : PeriodicLatticeSite Λ, holonomy A z ν = 0) (x : PeriodicLatticeSite Λ) :
    potential A ν (periodicLatticeShift x ν) - potential A ν x = A (x, ν) := by
  have hxz : coarseShift (zeroOut x ν) ((x ν).val) ν = x := coarseShift_zeroOut x ν
  have hstep : lineIntegralValue ((x ν).val + 1) A (zeroOut x ν) ν =
      lineIntegralValue ((x ν).val) A (zeroOut x ν) ν + A (x, ν) := by
    rw [lineIntegralValue_succ, hxz]
  simp only [potential, zeroOut_shift_self]
  by_cases hwrap : (x ν).val + 1 = Λ ν + 1
  · have hshift0 : ((periodicLatticeShift x ν) ν).val = 0 := by
      rw [shift_val, hwrap, Nat.mod_self]
    have h0 : holonomy A (zeroOut x ν) ν = 0 := hhol _
    simp only [holonomy] at h0
    rw [← hwrap] at h0
    rw [hshift0, lineIntegralValue_zero]
    linarith
  · have hlt : (x ν).val + 1 < Λ ν + 1 := by
      have := (x ν).isLt
      omega
    have hshift : ((periodicLatticeShift x ν) ν).val = (x ν).val + 1 := by
      rw [shift_val, Nat.mod_eq_of_lt hlt]
    rw [hshift]
    linarith

/-- If the `ν`-component of `A` is invariant under `μ`-shifts, so is the `ν`-potential
(`μ ≠ ν`). This is the bookkeeping that stops later gauge sweeps undoing earlier ones. -/
theorem potential_shiftInvariant {A : Bond Λ → ℝ} {μ ν : Fin 3} (h : μ ≠ ν)
    (hinv : ∀ y : PeriodicLatticeSite Λ, A (periodicLatticeShift y μ, ν) = A (y, ν))
    (x : PeriodicLatticeSite Λ) :
    potential A ν (periodicLatticeShift x μ) = potential A ν x := by
  simp only [potential, zeroOut_shift_ne x h, shift_apply_ne x μ ν (Ne.symm h)]
  simp only [lineIntegralValue]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (fun z : PeriodicLatticeSite Λ => periodicLatticeShift z ν)^[j]
      (periodicLatticeShift (zeroOut x ν) μ) =
      periodicLatticeShift ((fun z : PeriodicLatticeSite Λ => periodicLatticeShift z ν)^[j]
        (zeroOut x ν)) μ := shift_coarseShift (zeroOut x ν) j μ ν
  rw [hc]
  exact hinv _

/-- If `A` is curl-free and its `ν`-component vanishes identically, then EVERY component of `A` is
invariant under `ν`-shifts (immediate from `transport`). -/
theorem shiftInvariant_of_component_zero {A : Bond Λ → ℝ} (hA : CurlFree A) {ν : Fin 3}
    (hz : ∀ y : PeriodicLatticeSite Λ, A (y, ν) = 0) (x : PeriodicLatticeSite Λ) (μ : Fin 3) :
    A (periodicLatticeShift x ν, μ) = A (x, μ) := by
  have h := transport hA x μ ν
  rw [hz (periodicLatticeShift x μ), hz x] at h
  linarith

/-! ## §6. ONE AXIAL-GAUGE SWEEP, with the bookkeeping attached -/

/-- **One sweep.** Given a curl-free field with all holonomies zero, whose components in the
already-gauged set `D` vanish, there is a potential `f` such that `A - ∂₀f` additionally has
vanishing `ν`-component — AND still has vanishing components throughout `D`. -/
theorem gauge_step {A : Bond Λ → ℝ} (hA : CurlFree A)
    (hhol : ∀ (z : PeriodicLatticeSite Λ) (ρ : Fin 3), holonomy A z ρ = 0)
    (ν : Fin 3) (D : Fin 3 → Prop)
    (hD : ∀ δ, D δ → ∀ y : PeriodicLatticeSite Λ, A (y, δ) = 0) (hνD : ¬ D ν) :
    ∃ f : PeriodicLatticeSite Λ → ℝ,
      CurlFree (fun b => A b - gradValue f b) ∧
      (∀ (z : PeriodicLatticeSite Λ) (ρ : Fin 3),
        holonomy (fun b => A b - gradValue f b) z ρ = 0) ∧
      (∀ y : PeriodicLatticeSite Λ, A (y, ν) - gradValue f (y, ν) = 0) ∧
      (∀ δ, D δ → ∀ y : PeriodicLatticeSite Λ, A (y, δ) - gradValue f (y, δ) = 0) := by
  refine ⟨potential A ν, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [curlValue_sub, hA p, curlValue_gradValue]
    ring
  · intro z ρ
    rw [holonomy_sub, holonomy_gradValue, hhol z ρ]
    ring
  · intro y
    have h := potential_grad (A := A) ν (fun z => hhol z ν) y
    simp only [gradValue]
    linarith
  · intro δ hδ y
    have hδν : δ ≠ ν := fun hc => hνD (hc ▸ hδ)
    have hinv : ∀ w : PeriodicLatticeSite Λ, A (periodicLatticeShift w δ, ν) = A (w, ν) :=
      fun w => shiftInvariant_of_component_zero hA (hD δ hδ) w ν
    have hf : potential A ν (periodicLatticeShift y δ) = potential A ν y :=
      potential_shiftInvariant hδν hinv y
    simp only [gradValue, hD δ hδ y, hf]
    ring

/-! ## §7. THE THEOREM -/

/-- **THE DISCRETE POINCARÉ/HODGE LEMMA ON THE PERIODIC 3-TORUS.** A curl-free bond field is a
gradient plus a direction-constant field. The constants are NOT removable (`const_not_gradValue`,
§8). -/
theorem curlFree_eq_grad_add_const {A : Bond Λ → ℝ} (hA : CurlFree A) :
    ∃ (f : PeriodicLatticeSite Λ → ℝ) (c : Fin 3 → ℝ),
      ∀ b : Bond Λ, A b = f (periodicLatticeShift b.1 b.2) - f b.1 + c b.2 := by
  classical
  -- Step 0: remove the harmonic classes
  obtain ⟨c, hcurl0, hhol0⟩ :
      ∃ c : Fin 3 → ℝ, CurlFree (fun b : Bond Λ => A b - c b.2) ∧
        ∀ (z : PeriodicLatticeSite Λ) (ρ : Fin 3),
          holonomy (fun b : Bond Λ => A b - c b.2) z ρ = 0 := by
    refine ⟨fun ν => holonomy A (fun _ => 0) ν / ((Λ ν : ℝ) + 1), ?_, ?_⟩
    · intro p
      have hcv := curlValue_of_const (Λ := Λ)
        (fun ν => holonomy A (fun _ => 0) ν / ((Λ ν : ℝ) + 1)) p
      rw [curlValue_sub, hA p, hcv]
      ring
    · intro z ρ
      have hcf := holonomy_const_field (Λ := Λ)
        (fun ν => holonomy A (fun _ => 0) ν / ((Λ ν : ℝ) + 1)) z ρ
      have hb := holonomy_const hA z (fun _ => 0) ρ
      rw [holonomy_sub, hcf, hb]
      have hne : ((Λ ρ : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
  -- Sweep 1: direction 0
  obtain ⟨f0, hcurl1, hhol1, hz1, -⟩ :=
    gauge_step hcurl0 hhol0 0 (fun _ => False) (fun _ h => absurd h (by simp)) (by simp)
  -- Sweep 2: direction 1, preserving direction 0
  obtain ⟨f1, hcurl2, hhol2, hz2, hz2'⟩ :=
    gauge_step hcurl1 hhol1 1 (fun δ => δ = 0)
      (by rintro δ rfl y; exact hz1 y) (by decide)
  -- Sweep 3: direction 2, preserving directions 0 and 1
  obtain ⟨f2, -, -, hz3, hz3'⟩ :=
    gauge_step hcurl2 hhol2 2 (fun δ => δ = 0 ∨ δ = 1)
      (by
        rintro δ (rfl | rfl) y
        · exact hz2' 0 rfl y
        · exact hz2 y)
      (by decide)
  refine ⟨fun x => f0 x + f1 x + f2 x, c, ?_⟩
  rintro ⟨y, μ⟩
  have hall : (fun b : Bond Λ => A b - c b.2) (y, μ) - gradValue f0 (y, μ)
      - gradValue f1 (y, μ) - gradValue f2 (y, μ) = 0 := by
    have hcase : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
    rcases hcase μ with rfl | rfl | rfl
    · exact hz3' 0 (Or.inl rfl) y
    · exact hz3' 1 (Or.inr rfl) y
    · exact hz3 y
  simp only [gradValue] at hall ⊢
  linarith

/-! ## §8. NON-VACUITY AND SHARPNESS CONTROLS -/

/-- **must-not-fire: the conclusion is satisfied by the intended object.** Every gradient plus
constant IS curl-free, so `curlFree_eq_grad_add_const` characterises exactly the curl-free
fields — an equivalence, not a one-way weakening. -/
theorem curlFree_of_grad_add_const (f : PeriodicLatticeSite Λ → ℝ) (c : Fin 3 → ℝ) :
    CurlFree (fun b : Bond Λ => f (periodicLatticeShift b.1 b.2) - f b.1 + c b.2) := by
  intro p
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  simp only [curlValue]
  rw [periodicLatticeShift_comm p.1 hne]
  ring

/-- **must-fire: the constants are LOAD-BEARING.** The unit field in direction `ν` is curl-free but
is NOT a gradient — its holonomy is `Λ ν + 1 ≠ 0`, while every gradient has zero holonomy. So the
`c` in `curlFree_eq_grad_add_const` cannot be dropped: the naive Poincaré lemma is FALSE here, and
a proof that produced only `∃ f, A = ∂₀f` would be proving something false. -/
theorem const_not_gradValue (ν : Fin 3) (x : PeriodicLatticeSite Λ) :
    ¬ ∃ f : PeriodicLatticeSite Λ → ℝ,
        ∀ b : Bond Λ, (if b.2 = ν then (1 : ℝ) else 0) = gradValue f b := by
  rintro ⟨f, hf⟩
  have hfun : (fun b : Bond Λ => if b.2 = ν then (1 : ℝ) else 0) = gradValue f := funext hf
  have h0 : holonomy (fun b : Bond Λ => if b.2 = ν then (1 : ℝ) else 0) x ν = 0 := by
    rw [hfun]; exact holonomy_gradValue f x ν
  have hval : holonomy (fun b : Bond Λ => if b.2 = ν then (1 : ℝ) else 0) x ν =
      ((Λ ν : ℝ) + 1) := by
    have h := holonomy_const_field (Λ := Λ) (fun ρ => if ρ = ν then (1 : ℝ) else 0) x ν
    simpa using h
  rw [hval] at h0
  have hpos : (0 : ℝ) < (Λ ν : ℝ) + 1 := by positivity
  linarith

/-- **§DEGEN — THE CONTENT-EVAPORATION POINT, EXHIBITED AS A THEOREM.** On the one-site extent
`Λ = fun _ => 0` every `periodicLatticeShift` is the identity, so every `gradValue` is identically
`0` and the conclusion of `curlFree_eq_grad_add_const` is satisfied by `f := 0`, `c := A(x₀,·)`
**for EVERY bond field, curl-free or not** — the hypothesis is doing no work there. The theorem is
TRUE at that point and carries NO content; this declaration is the disclosure, kernel-checked
rather than asserted in prose. Two things it does NOT say:
* `const_not_gradValue` still FIRES at this point (`holonomy = Λ ν + 1 = 1 ≠ 0`), so even here the
  harmonic constant `c` is genuinely necessary — the degeneracy is that the GRADIENT part
  evaporates, not that the statement becomes false.
* The corresponding point for the consumer is `L μ + 1 = ell` in every direction, where the COARSE
  lattice is a single site and `coarseCurlValue` is identically `0`. There
  `U1Anchor.upperDegenerate_of_faithful` yields `deltaJQuadForm = 0` for EVERY `A0`. That is a
  consequence, not an artifact: with one coarse site the flat lift is the constant field `B` itself
  (`U1AnchorCoarse.lineCoarseRestrict_constBond`), which the faithful `Q_k` returns unchanged. -/
theorem singleSite_decomposition_is_free
    (A : Bond (fun _ => 0 : PeriodicLatticeExtent) → ℝ) :
    ∃ (f : PeriodicLatticeSite (fun _ => 0 : PeriodicLatticeExtent) → ℝ) (c : Fin 3 → ℝ),
      ∀ b : Bond (fun _ => 0 : PeriodicLatticeExtent),
        A b = f (periodicLatticeShift b.1 b.2) - f b.1 + c b.2 := by
  refine ⟨fun _ => 0, fun μ => A ((fun _ => 0), μ), ?_⟩
  rintro ⟨x, μ⟩
  have hx : x = (fun _ => 0) := by
    funext ν
    first
      | exact Fin.eq_zero (x ν)
      | exact Subsingleton.elim _ _
      | (apply Fin.ext
         have h := (x ν).isLt
         have h2 : ((fun _ => (0 : Fin 1)) ν).val = 0 := by decide
         omega)
  subst hx
  simp

#print axioms singleSite_decomposition_is_free

#print axioms curlFree_eq_grad_add_const
#print axioms curlFree_of_grad_add_const
#print axioms const_not_gradValue

end AdalyFormal.Balaban.U1AnchorPoincare
