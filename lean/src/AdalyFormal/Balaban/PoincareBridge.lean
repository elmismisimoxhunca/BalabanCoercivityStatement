/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.KernelSubspace
import AdalyFormal.Balaban.DiscretePoincare

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The Poincaré bridge — WORK IN PROGRESS (stub-safe: nothing is claimed until §7)
-/

namespace AdalyFormal.Balaban.PoincareBridge

open Finset
open AdalyFormal.Balaban.DiscretePoincare

/-! ## §1. The discrete cube of side `ell` in `d = 3`, and the cube Poincaré inequality -/

/-- The abstract discrete cube of side `ell` in three dimensions. -/
abbrev Cube (ell : ℕ) := Fin ell × Fin ell × Fin ell

/-- Direction-`0` line slice through `(b,c)`, as a function `ℕ → ℝ` so that
`DiscretePoincare`'s own `sumSq`/`dirichletEnergy`/`meanZero` apply verbatim. -/
noncomputable def slice0 (ell : ℕ) (Ψ : Cube ell → ℝ) (b c : Fin ell) : ℕ → ℝ :=
  fun k => if h : k < ell then Ψ (⟨k, h⟩, b, c) else 0

noncomputable def slice1 (ell : ℕ) (Ψ : Cube ell → ℝ) (a c : Fin ell) : ℕ → ℝ :=
  fun k => if h : k < ell then Ψ (a, ⟨k, h⟩, c) else 0

noncomputable def slice2 (ell : ℕ) (Ψ : Cube ell → ℝ) (a b : Fin ell) : ℕ → ℝ :=
  fun k => if h : k < ell then Ψ (a, b, ⟨k, h⟩) else 0

@[simp] theorem slice0_apply (ell : ℕ) (Ψ : Cube ell → ℝ) (b c a : Fin ell) :
    slice0 ell Ψ b c a.val = Ψ (a, b, c) := by
  simp only [slice0, dif_pos a.isLt, Fin.eta]

@[simp] theorem slice1_apply (ell : ℕ) (Ψ : Cube ell → ℝ) (a c b : Fin ell) :
    slice1 ell Ψ a c b.val = Ψ (a, b, c) := by
  simp only [slice1, dif_pos b.isLt, Fin.eta]

@[simp] theorem slice2_apply (ell : ℕ) (Ψ : Cube ell → ℝ) (a b c : Fin ell) :
    slice2 ell Ψ a b c.val = Ψ (a, b, c) := by
  simp only [slice2, dif_pos c.isLt, Fin.eta]

/-- `∑_p Ψ(p)^2` on the cube. -/
noncomputable def cSumSq (ell : ℕ) (Ψ : Cube ell → ℝ) : ℝ := ∑ p : Cube ell, (Ψ p) ^ 2

/-- Direction-`0` Dirichlet energy of the cube: the sum, over all direction-`0` lines, of the
Neumann (open-chain) Dirichlet energy of the line. -/
noncomputable def cE0 (ell : ℕ) (Ψ : Cube ell → ℝ) : ℝ :=
  ∑ b : Fin ell, ∑ c : Fin ell, dirichletEnergy ell (slice0 ell Ψ b c)

noncomputable def cE1 (ell : ℕ) (Ψ : Cube ell → ℝ) : ℝ :=
  ∑ a : Fin ell, ∑ c : Fin ell, dirichletEnergy ell (slice1 ell Ψ a c)

noncomputable def cE2 (ell : ℕ) (Ψ : Cube ell → ℝ) : ℝ :=
  ∑ a : Fin ell, ∑ b : Fin ell, dirichletEnergy ell (slice2 ell Ψ a b)

theorem cSumSq_nonneg (ell : ℕ) (Ψ : Cube ell → ℝ) : 0 ≤ cSumSq ell Ψ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cE0_nonneg (ell : ℕ) (Ψ : Cube ell → ℝ) : 0 ≤ cE0 ell Ψ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cE1_nonneg (ell : ℕ) (Ψ : Cube ell → ℝ) : 0 ≤ cE1 ell Ψ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cE2_nonneg (ell : ℕ) (Ψ : Cube ell → ℝ) : 0 ≤ cE2 ell Ψ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### §1.1 Rewriting `cSumSq` slicewise, in each of the three directions -/

theorem cSumSq_eq_slice0 (ell : ℕ) (Ψ : Cube ell → ℝ) :
    cSumSq ell Ψ = ∑ b : Fin ell, ∑ c : Fin ell, sumSq ell (slice0 ell Ψ b c) := by
  unfold cSumSq sumSq
  rw [Fintype.sum_prod_type]
  have h1 : ∀ a : Fin ell, ∑ q : Fin ell × Fin ell, (Ψ (a, q)) ^ 2
      = ∑ b : Fin ell, ∑ c : Fin ell, (Ψ (a, b, c)) ^ 2 := by
    intro a; rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun k => (slice0 ell Ψ b c k) ^ 2) ell]
  exact Finset.sum_congr rfl (fun a _ => by rw [slice0_apply])

theorem cSumSq_eq_slice1 (ell : ℕ) (Ψ : Cube ell → ℝ) :
    cSumSq ell Ψ = ∑ a : Fin ell, ∑ c : Fin ell, sumSq ell (slice1 ell Ψ a c) := by
  unfold cSumSq sumSq
  rw [Fintype.sum_prod_type]
  have h1 : ∀ a : Fin ell, ∑ q : Fin ell × Fin ell, (Ψ (a, q)) ^ 2
      = ∑ b : Fin ell, ∑ c : Fin ell, (Ψ (a, b, c)) ^ 2 := by
    intro a; rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun k => (slice1 ell Ψ a c k) ^ 2) ell]
  exact Finset.sum_congr rfl (fun b _ => by rw [slice1_apply])

theorem cSumSq_eq_slice2 (ell : ℕ) (Ψ : Cube ell → ℝ) :
    cSumSq ell Ψ = ∑ a : Fin ell, ∑ b : Fin ell, sumSq ell (slice2 ell Ψ a b) := by
  unfold cSumSq sumSq
  rw [Fintype.sum_prod_type]
  have h1 : ∀ a : Fin ell, ∑ q : Fin ell × Fin ell, (Ψ (a, q)) ^ 2
      = ∑ b : Fin ell, ∑ c : Fin ell, (Ψ (a, b, c)) ^ 2 := by
    intro a; rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun k => (slice2 ell Ψ a b k) ^ 2) ell]
  exact Finset.sum_congr rfl (fun c _ => by rw [slice2_apply])

/-! ### §1.2 The three coordinate-averaging operators -/

/-- `(A₀Ψ)(a,b,c) := (1/ell)·∑_{a'} Ψ(a',b,c)` — the average over the direction-`0` line. -/
noncomputable def A0 (ell : ℕ) (Ψ : Cube ell → ℝ) : Cube ell → ℝ :=
  fun p => (1 / (ell : ℝ)) * ∑ a : Fin ell, Ψ (a, p.2.1, p.2.2)

noncomputable def A1 (ell : ℕ) (Ψ : Cube ell → ℝ) : Cube ell → ℝ :=
  fun p => (1 / (ell : ℝ)) * ∑ b : Fin ell, Ψ (p.1, b, p.2.2)

noncomputable def A2 (ell : ℕ) (Ψ : Cube ell → ℝ) : Cube ell → ℝ :=
  fun p => (1 / (ell : ℝ)) * ∑ c : Fin ell, Ψ (p.1, p.2.1, c)

theorem A0_sub (ell : ℕ) (Ψ Φ : Cube ell → ℝ) :
    A0 ell (Ψ - Φ) = A0 ell Ψ - A0 ell Φ := by
  funext p
  simp only [A0, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem A1_sub (ell : ℕ) (Ψ Φ : Cube ell → ℝ) :
    A1 ell (Ψ - Φ) = A1 ell Ψ - A1 ell Φ := by
  funext p
  simp only [A1, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

/-- **`A₀` is an `ℓ²` contraction** (Cauchy–Schwarz). -/
theorem cSumSq_A0_le (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) :
    cSumSq ell (A0 ell Ψ) ≤ cSumSq ell Ψ := by
  have hpos : (0 : ℝ) < ell := by exact_mod_cast hell
  rw [cSumSq_eq_slice0, cSumSq_eq_slice0]
  refine Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => ?_))
  -- slicewise: the slice of `A0 Ψ` is constant `= mean of the slice of Ψ`
  have hval : ∀ a : Fin ell, slice0 ell (A0 ell Ψ) b c a.val
      = (1 / (ell : ℝ)) * ∑ a' : Fin ell, slice0 ell Ψ b c a'.val := by
    intro a
    rw [slice0_apply]
    simp only [A0]
    exact congrArg _ (Finset.sum_congr rfl (fun a' _ => (slice0_apply ell Ψ b c a').symm))
  unfold sumSq
  rw [← Fin.sum_univ_eq_sum_range (fun k => (slice0 ell (A0 ell Ψ) b c k) ^ 2) ell,
    ← Fin.sum_univ_eq_sum_range (fun k => (slice0 ell Ψ b c k) ^ 2) ell]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin ell))) => by
    rw [hval a])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hCS : (∑ a' : Fin ell, slice0 ell Ψ b c a'.val) ^ 2
      ≤ (ell : ℝ) * ∑ a' : Fin ell, (slice0 ell Ψ b c a'.val) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin ell)))
      (f := fun a' : Fin ell => slice0 ell Ψ b c a'.val)
    simpa using this
  have hexp : (ell : ℝ) * ((1 / (ell : ℝ)) * ∑ a' : Fin ell, slice0 ell Ψ b c a'.val) ^ 2
      = (1 / (ell : ℝ)) * (∑ a' : Fin ell, slice0 ell Ψ b c a'.val) ^ 2 := by
    field_simp
  rw [hexp]
  calc (1 / (ell : ℝ)) * (∑ a' : Fin ell, slice0 ell Ψ b c a'.val) ^ 2
      ≤ (1 / (ell : ℝ)) * ((ell : ℝ) * ∑ a' : Fin ell, (slice0 ell Ψ b c a'.val) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = ∑ a' : Fin ell, (slice0 ell Ψ b c a'.val) ^ 2 := by field_simp

/-- **`A₁` is an `ℓ²` contraction.** -/
theorem cSumSq_A1_le (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) :
    cSumSq ell (A1 ell Ψ) ≤ cSumSq ell Ψ := by
  have hpos : (0 : ℝ) < ell := by exact_mod_cast hell
  rw [cSumSq_eq_slice1, cSumSq_eq_slice1]
  refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ => ?_))
  have hval : ∀ b : Fin ell, slice1 ell (A1 ell Ψ) a c b.val
      = (1 / (ell : ℝ)) * ∑ b' : Fin ell, slice1 ell Ψ a c b'.val := by
    intro b
    rw [slice1_apply]
    simp only [A1]
    exact congrArg _ (Finset.sum_congr rfl (fun b' _ => (slice1_apply ell Ψ a c b').symm))
  unfold sumSq
  rw [← Fin.sum_univ_eq_sum_range (fun k => (slice1 ell (A1 ell Ψ) a c k) ^ 2) ell,
    ← Fin.sum_univ_eq_sum_range (fun k => (slice1 ell Ψ a c k) ^ 2) ell]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset (Fin ell))) => by
    rw [hval b])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hCS : (∑ b' : Fin ell, slice1 ell Ψ a c b'.val) ^ 2
      ≤ (ell : ℝ) * ∑ b' : Fin ell, (slice1 ell Ψ a c b'.val) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin ell)))
      (f := fun b' : Fin ell => slice1 ell Ψ a c b'.val)
    simpa using this
  have hexp : (ell : ℝ) * ((1 / (ell : ℝ)) * ∑ b' : Fin ell, slice1 ell Ψ a c b'.val) ^ 2
      = (1 / (ell : ℝ)) * (∑ b' : Fin ell, slice1 ell Ψ a c b'.val) ^ 2 := by
    field_simp
  rw [hexp]
  calc (1 / (ell : ℝ)) * (∑ b' : Fin ell, slice1 ell Ψ a c b'.val) ^ 2
      ≤ (1 / (ell : ℝ)) * ((ell : ℝ) * ∑ b' : Fin ell, (slice1 ell Ψ a c b'.val) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = ∑ b' : Fin ell, (slice1 ell Ψ a c b'.val) ^ 2 := by field_simp

theorem A2_sub (ell : ℕ) (Ψ Φ : Cube ell → ℝ) :
    A2 ell (Ψ - Φ) = A2 ell Ψ - A2 ell Φ := by
  funext p
  simp only [A2, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

/-! ### §1.3 The one-dimensional Neumann Poincaré inequality, applied line by line.

This is the ONLY place where genuinely analytic content enters: `DiscretePoincare`'s own
`discrete_poincare_crude` — a bound for the OPEN (Neumann) chain — is applied verbatim, once per
coordinate line of the cube. -/

/-- Slicewise step: a mean-zero `φ` with the SAME consecutive differences as `ψ` on `range (n-1)`
inherits `discrete_poincare_crude`'s bound, stated against `ψ`'s Dirichlet energy. -/
theorem sumSq_le_of_meanZero_of_diff (n : ℕ) (φ ψ : ℕ → ℝ) (hmz : meanZero n φ)
    (hdiff : ∀ i ∈ range (n - 1), φ (i + 1) - φ i = ψ (i + 1) - ψ i) :
    sumSq n φ ≤ ((n : ℝ) * (n - 1) / 2) * dirichletEnergy n ψ := by
  have hE : dirichletEnergy n φ = dirichletEnergy n ψ := by
    unfold dirichletEnergy
    exact Finset.sum_congr rfl (fun i hi => by rw [hdiff i hi])
  rw [← hE]
  exact discrete_poincare_crude n φ hmz

theorem slice0_sub_A0_meanZero (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) (b c : Fin ell) :
    meanZero ell (slice0 ell (Ψ - A0 ell Ψ) b c) := by
  have hne : (ell : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    exact ne_of_gt this
  unfold meanZero
  rw [← Fin.sum_univ_eq_sum_range (fun k => slice0 ell (Ψ - A0 ell Ψ) b c k) ell]
  have hterm : ∀ a : Fin ell, slice0 ell (Ψ - A0 ell Ψ) b c a.val
      = Ψ (a, b, c) - (1 / (ell : ℝ)) * ∑ a' : Fin ell, Ψ (a', b, c) := by
    intro a
    rw [slice0_apply]
    simp only [Pi.sub_apply, A0]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin ell))) => hterm a)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem slice1_sub_A1_meanZero (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) (a c : Fin ell) :
    meanZero ell (slice1 ell (Ψ - A1 ell Ψ) a c) := by
  have hne : (ell : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    exact ne_of_gt this
  unfold meanZero
  rw [← Fin.sum_univ_eq_sum_range (fun k => slice1 ell (Ψ - A1 ell Ψ) a c k) ell]
  have hterm : ∀ b : Fin ell, slice1 ell (Ψ - A1 ell Ψ) a c b.val
      = Ψ (a, b, c) - (1 / (ell : ℝ)) * ∑ b' : Fin ell, Ψ (a, b', c) := by
    intro b
    rw [slice1_apply]
    simp only [Pi.sub_apply, A1]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset (Fin ell))) => hterm b)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem slice2_sub_A2_meanZero (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) (a b : Fin ell) :
    meanZero ell (slice2 ell (Ψ - A2 ell Ψ) a b) := by
  have hne : (ell : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    exact ne_of_gt this
  unfold meanZero
  rw [← Fin.sum_univ_eq_sum_range (fun k => slice2 ell (Ψ - A2 ell Ψ) a b k) ell]
  have hterm : ∀ c : Fin ell, slice2 ell (Ψ - A2 ell Ψ) a b c.val
      = Ψ (a, b, c) - (1 / (ell : ℝ)) * ∑ c' : Fin ell, Ψ (a, b, c') := by
    intro c
    rw [slice2_apply]
    simp only [Pi.sub_apply, A2]
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ (Finset.univ : Finset (Fin ell))) => hterm c)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem slice0_sub_A0_diff (ell : ℕ) (Ψ : Cube ell → ℝ) (b c : Fin ell) (i : ℕ)
    (hi : i ∈ range (ell - 1)) :
    slice0 ell (Ψ - A0 ell Ψ) b c (i + 1) - slice0 ell (Ψ - A0 ell Ψ) b c i
      = slice0 ell Ψ b c (i + 1) - slice0 ell Ψ b c i := by
  rw [Finset.mem_range] at hi
  have h1 : i < ell := by omega
  have h2 : i + 1 < ell := by omega
  simp only [slice0, dif_pos h1, dif_pos h2, Pi.sub_apply, A0]
  ring

theorem slice1_sub_A1_diff (ell : ℕ) (Ψ : Cube ell → ℝ) (a c : Fin ell) (i : ℕ)
    (hi : i ∈ range (ell - 1)) :
    slice1 ell (Ψ - A1 ell Ψ) a c (i + 1) - slice1 ell (Ψ - A1 ell Ψ) a c i
      = slice1 ell Ψ a c (i + 1) - slice1 ell Ψ a c i := by
  rw [Finset.mem_range] at hi
  have h1 : i < ell := by omega
  have h2 : i + 1 < ell := by omega
  simp only [slice1, dif_pos h1, dif_pos h2, Pi.sub_apply, A1]
  ring

theorem slice2_sub_A2_diff (ell : ℕ) (Ψ : Cube ell → ℝ) (a b : Fin ell) (i : ℕ)
    (hi : i ∈ range (ell - 1)) :
    slice2 ell (Ψ - A2 ell Ψ) a b (i + 1) - slice2 ell (Ψ - A2 ell Ψ) a b i
      = slice2 ell Ψ a b (i + 1) - slice2 ell Ψ a b i := by
  rw [Finset.mem_range] at hi
  have h1 : i < ell := by omega
  have h2 : i + 1 < ell := by omega
  simp only [slice2, dif_pos h1, dif_pos h2, Pi.sub_apply, A2]
  ring

theorem cSumSq_sub_A0_le (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) :
    cSumSq ell (Ψ - A0 ell Ψ) ≤ ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE0 ell Ψ := by
  rw [cSumSq_eq_slice0, cE0, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun c _ => ?_)
  exact sumSq_le_of_meanZero_of_diff ell _ _ (slice0_sub_A0_meanZero ell hell Ψ b c)
    (slice0_sub_A0_diff ell Ψ b c)

theorem cSumSq_sub_A1_le (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) :
    cSumSq ell (Ψ - A1 ell Ψ) ≤ ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE1 ell Ψ := by
  rw [cSumSq_eq_slice1, cE1, Finset.mul_sum]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun c _ => ?_)
  exact sumSq_le_of_meanZero_of_diff ell _ _ (slice1_sub_A1_meanZero ell hell Ψ a c)
    (slice1_sub_A1_diff ell Ψ a c)

theorem cSumSq_sub_A2_le (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ) :
    cSumSq ell (Ψ - A2 ell Ψ) ≤ ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE2 ell Ψ := by
  rw [cSumSq_eq_slice2, cE2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  exact sumSq_le_of_meanZero_of_diff ell _ _ (slice2_sub_A2_meanZero ell hell Ψ a b)
    (slice2_sub_A2_diff ell Ψ a b)

/-! ### §1.4 The cube Poincaré inequality -/

theorem cube_sum_eq_triple (ell : ℕ) (Ψ : Cube ell → ℝ) :
    ∑ p : Cube ell, Ψ p = ∑ a : Fin ell, ∑ b : Fin ell, ∑ c : Fin ell, Ψ (a, b, c) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun a _ => by rw [Fintype.sum_prod_type])

theorem A0_A1_A2_eq_zero (ell : ℕ) (Ψ : Cube ell → ℝ)
    (hmz : ∑ p : Cube ell, Ψ p = 0) : A0 ell (A1 ell (A2 ell Ψ)) = 0 := by
  have key : ∑ a : Fin ell, ∑ b : Fin ell, ∑ c : Fin ell, Ψ (a, b, c) = 0 := by
    rw [← cube_sum_eq_triple]; exact hmz
  funext p
  simp only [A0, A1, A2, Pi.zero_apply]
  have h3 : ∀ a : Fin ell,
      (1 / (ell : ℝ)) * ∑ b : Fin ell, (1 / (ell : ℝ)) * ∑ c : Fin ell, Ψ (a, b, c)
        = (1 / (ell : ℝ)) ^ 2 * ∑ b : Fin ell, ∑ c : Fin ell, Ψ (a, b, c) := by
    intro a
    rw [← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin ell))) => h3 a),
    ← Finset.mul_sum, key, mul_zero, mul_zero]

/-- Elementary: `(x+y+z)² ≤ 3(x²+y²+z²)` — the exact source of the factor `3` (one per coordinate
direction) in the cube Poincaré constant. -/
theorem sq_add_three_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- The telescoping decomposition `Ψ = (Ψ-A₀Ψ) + A₀(Ψ-A₁Ψ) + A₀A₁(Ψ-A₂Ψ) + A₀A₁A₂Ψ`, with the
last term killed by the mean-zero hypothesis. -/
theorem cube_decomposition (ell : ℕ) (Ψ : Cube ell → ℝ) (p : Cube ell)
    (hz : A0 ell (A1 ell (A2 ell Ψ)) = 0) :
    Ψ p = (Ψ - A0 ell Ψ) p + (A0 ell (Ψ - A1 ell Ψ)) p
        + (A0 ell (A1 ell (Ψ - A2 ell Ψ))) p := by
  have hzp : (A0 ell (A1 ell (A2 ell Ψ))) p = 0 := by rw [hz]; rfl
  simp only [A0_sub, A1_sub, Pi.sub_apply]
  linarith [hzp]

/-- **THE CUBE POINCARÉ INEQUALITY.** For a function on the discrete `ell × ell × ell` cube with
total sum zero:
`∑_p Ψ(p)² ≤ (3·ell·(ell-1)/2) · (E₀ + E₁ + E₂)`,
where `E_μ` is the sum, over all coordinate lines in direction `μ`, of the OPEN (Neumann) chain
Dirichlet energy of that line. The constant is composed as `3` (three coordinate directions, from
`(x+y+z)² ≤ 3(x²+y²+z²)`) times `ell·(ell-1)/2` (`DiscretePoincare.discrete_poincare_crude`'s own
one-dimensional constant on `ell` points), with NO further factors: the three averaging operators
`A₀`, `A₁` are `ℓ²`-contractions and contribute `1` each. -/
theorem cube_poincare (ell : ℕ) (hell : 1 ≤ ell) (Ψ : Cube ell → ℝ)
    (hmz : ∑ p : Cube ell, Ψ p = 0) :
    cSumSq ell Ψ ≤ (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2)
      * (cE0 ell Ψ + cE1 ell Ψ + cE2 ell Ψ) := by
  have hz := A0_A1_A2_eq_zero ell Ψ hmz
  have hptwise : ∀ p : Cube ell, (Ψ p) ^ 2
      ≤ 3 * (((Ψ - A0 ell Ψ) p) ^ 2 + ((A0 ell (Ψ - A1 ell Ψ)) p) ^ 2
          + ((A0 ell (A1 ell (Ψ - A2 ell Ψ))) p) ^ 2) := by
    intro p
    rw [cube_decomposition ell Ψ p hz]
    exact sq_add_three_le _ _ _
  have hsplit : cSumSq ell Ψ ≤ 3 * (cSumSq ell (Ψ - A0 ell Ψ)
      + cSumSq ell (A0 ell (Ψ - A1 ell Ψ)) + cSumSq ell (A0 ell (A1 ell (Ψ - A2 ell Ψ)))) := by
    unfold cSumSq
    calc ∑ p : Cube ell, (Ψ p) ^ 2
        ≤ ∑ p : Cube ell, 3 * (((Ψ - A0 ell Ψ) p) ^ 2 + ((A0 ell (Ψ - A1 ell Ψ)) p) ^ 2
            + ((A0 ell (A1 ell (Ψ - A2 ell Ψ))) p) ^ 2) :=
          Finset.sum_le_sum (fun p _ => hptwise p)
      _ = 3 * (∑ p : Cube ell, ((Ψ - A0 ell Ψ) p) ^ 2
            + ∑ p : Cube ell, ((A0 ell (Ψ - A1 ell Ψ)) p) ^ 2
            + ∑ p : Cube ell, ((A0 ell (A1 ell (Ψ - A2 ell Ψ))) p) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h0 : cSumSq ell (Ψ - A0 ell Ψ) ≤ ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE0 ell Ψ :=
    cSumSq_sub_A0_le ell hell Ψ
  have h1 : cSumSq ell (A0 ell (Ψ - A1 ell Ψ))
      ≤ ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE1 ell Ψ :=
    le_trans (cSumSq_A0_le ell hell _) (cSumSq_sub_A1_le ell hell Ψ)
  have h2 : cSumSq ell (A0 ell (A1 ell (Ψ - A2 ell Ψ)))
      ≤ ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE2 ell Ψ :=
    le_trans (cSumSq_A0_le ell hell _)
      (le_trans (cSumSq_A1_le ell hell _) (cSumSq_sub_A2_le ell hell Ψ))
  have hring : (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2) * (cE0 ell Ψ + cE1 ell Ψ + cE2 ell Ψ)
      = 3 * (((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE0 ell Ψ
          + ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE1 ell Ψ
          + ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * cE2 ell Ψ) := by ring
  rw [hring]
  linarith [hsplit, h0, h1, h2]


/-! ## §2. Transporting the cube onto a lattice block

`AdmissibleSubspace.blockOf y ell` is an axis-aligned coordinate box; `chart y ell` is the explicit
bijection `Cube ell ≃ blockOf y ell` realizing it (the same bijection `card_blockOf` uses to count
the block, re-derived here in the `Cube` coordinates the §1 argument needs). -/

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

/-- The cube coordinate in lattice direction `μ`. -/
def cubeIdx {ell : ℕ} (p : Cube ell) (μ : Fin 3) : ℕ :=
  if μ = 0 then p.1.val else if μ = 1 then p.2.1.val else p.2.2.val

theorem cubeIdx_lt {ell : ℕ} (p : Cube ell) (μ : Fin 3) : cubeIdx p μ < ell := by
  unfold cubeIdx
  split_ifs
  · exact p.1.isLt
  · exact p.2.1.isLt
  · exact p.2.2.isLt

@[simp] theorem cubeIdx_zero {ell : ℕ} (p : Cube ell) : cubeIdx p 0 = p.1.val := by
  unfold cubeIdx
  rw [if_pos rfl]

@[simp] theorem cubeIdx_one {ell : ℕ} (p : Cube ell) : cubeIdx p 1 = p.2.1.val := by
  unfold cubeIdx
  rw [if_neg (by decide), if_pos rfl]

@[simp] theorem cubeIdx_two {ell : ℕ} (p : Cube ell) : cubeIdx p 2 = p.2.2.val := by
  unfold cubeIdx
  rw [if_neg (by decide), if_neg (by decide)]

variable {L : PeriodicLatticeExtent}

/-- **The block chart**: the cube point `p` placed at block corner `y`. Total (the `%` makes it
carry no proof argument); `chart_val` shows the modulus is inert exactly when the block fits inside
the periodic extent, which every `CoarseLattice` corner does (`coarseLattice_fits`). -/
def chart (y : PeriodicLatticeSite L) (ell : ℕ) (p : Cube ell) : PeriodicLatticeSite L :=
  fun μ => ⟨((y μ).val + cubeIdx p μ) % (L μ + 1), Nat.mod_lt _ (by omega)⟩

theorem chart_val {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) (p : Cube ell) (μ : Fin 3) :
    ((chart y ell p) μ).val = (y μ).val + cubeIdx p μ := by
  have h1 := cubeIdx_lt p μ
  have h2 := hfit μ
  show ((y μ).val + cubeIdx p μ) % (L μ + 1) = (y μ).val + cubeIdx p μ
  exact Nat.mod_eq_of_lt (by omega)

theorem chart_mem_block {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) (p : Cube ell) :
    chart y ell p ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  rw [chart_val hfit]
  have := cubeIdx_lt p μ
  omega

theorem chart_injective {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) : Function.Injective (chart y ell) := by
  intro p q h
  have key : ∀ μ, cubeIdx p μ = cubeIdx q μ := by
    intro μ
    have hv : ((chart y ell p) μ).val = ((chart y ell q) μ).val := by rw [h]
    rw [chart_val hfit p μ, chart_val hfit q μ] at hv
    omega
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  rw [cubeIdx_zero, cubeIdx_zero] at h0
  rw [cubeIdx_one, cubeIdx_one] at h1
  rw [cubeIdx_two, cubeIdx_two] at h2
  simp only [Prod.ext_iff, Fin.ext_iff]
  exact ⟨h0, h1, h2⟩

/-- **The chart's image is exactly the block** — proved by cardinality against
`AdmissibleSubspace.card_blockOf` (LAW-19 reuse of the already-proved `|B(y)| = ell³`), not by
re-deriving the surjection. -/
theorem chart_image {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) :
    Finset.image (chart y ell) Finset.univ = blockOf y ell := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨p, rfl⟩ := hx
    exact chart_mem_block hfit p
  · rw [card_blockOf y ell hfit, Finset.card_image_of_injective _ (chart_injective hfit),
      Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact le_of_eq (by ring)

/-- Every `CoarseLattice` corner's block genuinely fits inside the periodic extent, so the modulus
in `chart` is inert on exactly the corners this file uses. -/
theorem coarseLattice_fits {ell : ℕ} (hdvd : ∀ μ, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    ∀ μ, (y μ).val + ell ≤ L μ + 1 := by
  rw [mem_CoarseLattice] at hy
  intro μ
  obtain ⟨m, hm⟩ := hdvd μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (hy μ)
  have hlt := (y μ).isLt
  rw [hk, hm] at hlt ⊢
  have hkm : k < m := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmul : ell * m ≤ ell * k := Nat.mul_le_mul_left ell hcon
    omega
  calc ell * k + ell = ell * (k + 1) := by ring
    _ ≤ ell * m := Nat.mul_le_mul_left ell (by omega)

/-! ### §2.1 The three directional index maps, and the identification of `cE_μ` -/

/-- Index set of a directional "step": `Fin (ell-1)` positions along the stepping direction,
`Fin ell × Fin ell` transverse positions. Shared by all three directions. -/
abbrev StepIdx (ell : ℕ) := Fin (ell - 1) × Fin ell × Fin ell

def cubeOf0 {ell : ℕ} (j : StepIdx ell) : Cube ell :=
  (⟨j.1.val, by have := j.1.isLt; omega⟩, j.2.1, j.2.2)

def cubeOf0' {ell : ℕ} (j : StepIdx ell) : Cube ell :=
  (⟨j.1.val + 1, by have := j.1.isLt; omega⟩, j.2.1, j.2.2)

def cubeOf1 {ell : ℕ} (j : StepIdx ell) : Cube ell :=
  (j.2.1, ⟨j.1.val, by have := j.1.isLt; omega⟩, j.2.2)

def cubeOf1' {ell : ℕ} (j : StepIdx ell) : Cube ell :=
  (j.2.1, ⟨j.1.val + 1, by have := j.1.isLt; omega⟩, j.2.2)

def cubeOf2 {ell : ℕ} (j : StepIdx ell) : Cube ell :=
  (j.2.1, j.2.2, ⟨j.1.val, by have := j.1.isLt; omega⟩)

def cubeOf2' {ell : ℕ} (j : StepIdx ell) : Cube ell :=
  (j.2.1, j.2.2, ⟨j.1.val + 1, by have := j.1.isLt; omega⟩)

theorem cubeOf0_injective {ell : ℕ} : Function.Injective (cubeOf0 (ell := ell)) := by
  intro j j' h
  simp only [cubeOf0, Prod.ext_iff, Fin.ext_iff] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem cubeOf1_injective {ell : ℕ} : Function.Injective (cubeOf1 (ell := ell)) := by
  intro j j' h
  simp only [cubeOf1, Prod.ext_iff, Fin.ext_iff] at h ⊢
  exact ⟨h.2.1, h.1, h.2.2⟩

theorem cubeOf2_injective {ell : ℕ} : Function.Injective (cubeOf2 (ell := ell)) := by
  intro j j' h
  simp only [cubeOf2, Prod.ext_iff, Fin.ext_iff] at h ⊢
  exact ⟨h.2.2, h.1, h.2.1⟩

/-- Reordering helper: `∑_b ∑_c ∑_k = ∑_k ∑_b ∑_c`. -/
theorem sum_swap3 {ell : ℕ} (g : Fin (ell - 1) → Fin ell → Fin ell → ℝ) :
    (∑ b : Fin ell, ∑ c : Fin ell, ∑ k : Fin (ell - 1), g k b c)
      = ∑ k : Fin (ell - 1), ∑ b : Fin ell, ∑ c : Fin ell, g k b c := by
  have step1 : ∀ b : Fin ell, (∑ c : Fin ell, ∑ k : Fin (ell - 1), g k b c)
      = ∑ k : Fin (ell - 1), ∑ c : Fin ell, g k b c := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset (Fin ell))) => step1 b)]
  exact Finset.sum_comm

theorem stepIdx_sum {ell : ℕ} (f : StepIdx ell → ℝ) :
    (∑ j : StepIdx ell, f j) = ∑ k : Fin (ell - 1), ∑ b : Fin ell, ∑ c : Fin ell, f (k, b, c) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun k _ => by rw [Fintype.sum_prod_type])

theorem cE0_eq_stepIdx (ell : ℕ) (Ψ : Cube ell → ℝ) :
    cE0 ell Ψ = ∑ j : StepIdx ell, (Ψ (cubeOf0' j) - Ψ (cubeOf0 j)) ^ 2 := by
  rw [stepIdx_sum]
  unfold cE0 dirichletEnergy
  rw [← sum_swap3 (fun k b c => (Ψ (cubeOf0' (k, b, c)) - Ψ (cubeOf0 (k, b, c))) ^ 2)]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => (slice0 ell Ψ b c (i + 1) - slice0 ell Ψ b c i) ^ 2) (ell - 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk := k.isLt
  have h0 : k.val < ell := by omega
  have h1 : k.val + 1 < ell := by omega
  simp only [slice0, dif_pos h0, dif_pos h1, cubeOf0, cubeOf0']

theorem cE1_eq_stepIdx (ell : ℕ) (Ψ : Cube ell → ℝ) :
    cE1 ell Ψ = ∑ j : StepIdx ell, (Ψ (cubeOf1' j) - Ψ (cubeOf1 j)) ^ 2 := by
  rw [stepIdx_sum]
  unfold cE1 dirichletEnergy
  rw [← sum_swap3 (fun k b c => (Ψ (cubeOf1' (k, b, c)) - Ψ (cubeOf1 (k, b, c))) ^ 2)]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => (slice1 ell Ψ b c (i + 1) - slice1 ell Ψ b c i) ^ 2) (ell - 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk := k.isLt
  have h0 : k.val < ell := by omega
  have h1 : k.val + 1 < ell := by omega
  simp only [slice1, dif_pos h0, dif_pos h1, cubeOf1, cubeOf1']

theorem cE2_eq_stepIdx (ell : ℕ) (Ψ : Cube ell → ℝ) :
    cE2 ell Ψ = ∑ j : StepIdx ell, (Ψ (cubeOf2' j) - Ψ (cubeOf2 j)) ^ 2 := by
  rw [stepIdx_sum]
  unfold cE2 dirichletEnergy
  rw [← sum_swap3 (fun k b c => (Ψ (cubeOf2' (k, b, c)) - Ψ (cubeOf2 (k, b, c))) ^ 2)]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => (slice2 ell Ψ b c (i + 1) - slice2 ell Ψ b c i) ^ 2) (ell - 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk := k.isLt
  have h0 : k.val < ell := by omega
  have h1 : k.val + 1 < ell := by omega
  simp only [slice2, dif_pos h0, dif_pos h1, cubeOf2, cubeOf2']

/-! ### §2.2 A cube step maps to a genuine lattice bond -/

theorem shift_val_ne (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : ν ≠ μ) :
    (periodicLatticeShift x μ) ν = x ν := by
  rw [periodicLatticeShift]
  exact Function.update_of_ne hne _ _

theorem shift_val_self (x : PeriodicLatticeSite L) (μ : Fin 3) (h : (x μ).val + 1 < L μ + 1) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
  rw [periodicLatticeShift, Function.update_self]
  have hlt : x μ < Fin.last (L μ) := by
    rw [Fin.lt_def, Fin.val_last]
    omega
  exact Fin.val_add_one_of_lt hlt

theorem chart_step0 {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) (j : StepIdx ell) :
    chart y ell (cubeOf0' j) = periodicLatticeShift (chart y ell (cubeOf0 j)) 0 := by
  have hk := j.1.isLt
  have hfit0 := hfit 0
  have hbase : ((chart y ell (cubeOf0 j)) 0).val = (y 0).val + j.1.val := by
    rw [chart_val hfit, cubeIdx_zero]
    all_goals simp only [cubeOf0]
  have hroom : ((chart y ell (cubeOf0 j)) 0).val + 1 < L 0 + 1 := by
    rw [hbase]; omega
  funext ν
  by_cases hν : ν = 0
  · subst hν
    apply Fin.ext
    rw [chart_val hfit, cubeIdx_zero, shift_val_self _ _ hroom, hbase]
    all_goals simp only [cubeOf0']
    all_goals omega
  · rw [shift_val_ne _ hν]
    apply Fin.ext
    rw [chart_val hfit, chart_val hfit]
    have hidx : cubeIdx (cubeOf0' j) ν = cubeIdx (cubeOf0 j) ν := by
      unfold cubeIdx
      rw [if_neg hν]
      split_ifs <;> rfl
    rw [hidx]

theorem chart_step1 {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) (j : StepIdx ell) :
    chart y ell (cubeOf1' j) = periodicLatticeShift (chart y ell (cubeOf1 j)) 1 := by
  have hk := j.1.isLt
  have hfit1 := hfit 1
  have hbase : ((chart y ell (cubeOf1 j)) 1).val = (y 1).val + j.1.val := by
    rw [chart_val hfit, cubeIdx_one]
    all_goals simp only [cubeOf1]
  have hroom : ((chart y ell (cubeOf1 j)) 1).val + 1 < L 1 + 1 := by
    rw [hbase]; omega
  funext ν
  by_cases hν : ν = 1
  · subst hν
    apply Fin.ext
    rw [chart_val hfit, cubeIdx_one, shift_val_self _ _ hroom, hbase]
    all_goals simp only [cubeOf1']
    all_goals omega
  · rw [shift_val_ne _ hν]
    apply Fin.ext
    rw [chart_val hfit, chart_val hfit]
    have hidx : cubeIdx (cubeOf1' j) ν = cubeIdx (cubeOf1 j) ν := by
      unfold cubeIdx
      by_cases hν0 : ν = 0
      · rw [if_pos hν0, if_pos hν0]; rfl
      · rw [if_neg hν0, if_neg hν0, if_neg hν, if_neg hν]; rfl
    rw [hidx]

theorem chart_step2 {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) (j : StepIdx ell) :
    chart y ell (cubeOf2' j) = periodicLatticeShift (chart y ell (cubeOf2 j)) 2 := by
  have hk := j.1.isLt
  have hfit2 := hfit 2
  have hbase : ((chart y ell (cubeOf2 j)) 2).val = (y 2).val + j.1.val := by
    rw [chart_val hfit, cubeIdx_two]
    all_goals simp only [cubeOf2]
  have hroom : ((chart y ell (cubeOf2 j)) 2).val + 1 < L 2 + 1 := by
    rw [hbase]; omega
  funext ν
  by_cases hν : ν = 2
  · subst hν
    apply Fin.ext
    rw [chart_val hfit, cubeIdx_two, shift_val_self _ _ hroom, hbase]
    all_goals simp only [cubeOf2']
    all_goals omega
  · rw [shift_val_ne _ hν]
    apply Fin.ext
    rw [chart_val hfit, chart_val hfit]
    have hidx : cubeIdx (cubeOf2' j) ν = cubeIdx (cubeOf2 j) ν := by
      unfold cubeIdx
      by_cases hν0 : ν = 0
      · rw [if_pos hν0, if_pos hν0]; rfl
      · by_cases hν1 : ν = 1
        · rw [if_neg hν0, if_neg hν0, if_pos hν1, if_pos hν1]; rfl
        · exfalso
          have h3 := ν.isLt
          have e0 : ν.val ≠ 0 := fun hh => hν0 (Fin.ext hh)
          have e1 : ν.val ≠ 1 := fun hh => hν1 (Fin.ext hh)
          have e2 : ν.val ≠ 2 := fun hh => hν (Fin.ext hh)
          omega
    rw [hidx]

/-! ## §3. The disjoint block decomposition of the torus, and the edge-disjointness assembly

This is CMP89 (2.26)'s own super-additivity move, made explicit: the periodic Dirichlet form
dominates the sum of the block-local (Neumann) Dirichlet forms, because the intra-block bonds of
distinct blocks are DISJOINT subsets of the ambient bond set and every dropped cross-block term is
a square. -/

theorem blocks_disjoint (ell : ℕ) :
    ((CoarseLattice L ell : Finset (PeriodicLatticeSite L)) :
        Set (PeriodicLatticeSite L)).PairwiseDisjoint (fun y => blockOf y ell) := by
  intro y hy y' hy' hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  exact hne (coarseLattice_unique ell (by simpa using hy) (by simpa using hy') hx hx')

theorem univ_eq_biUnion_blocks (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1)) :
    (Finset.univ : Finset (PeriodicLatticeSite L))
      = (CoarseLattice L ell).biUnion (fun y => blockOf y ell) := by
  ext x
  simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
  obtain ⟨y, hy, hx⟩ := coarseLattice_exists ell hell hdvd x
  exact ⟨y, hy, hx⟩

theorem sum_eq_blocks (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1))
    (f : PeriodicLatticeSite L → ℝ) :
    ∑ x : PeriodicLatticeSite L, f x = ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, f x := by
  conv_lhs => rw [univ_eq_biUnion_blocks ell hell hdvd]
  exact Finset.sum_biUnion (blocks_disjoint ell)

theorem sum_block_eq_cube {y : PeriodicLatticeSite L} {ell : ℕ}
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) (f : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ blockOf y ell, f x = ∑ p : Cube ell, f (chart y ell p) := by
  rw [← chart_image hfit, Finset.sum_image]
  intro x _ z _ h
  exact chart_injective hfit h

/-- The bond carrying a directional cube step, as a function of the block corner and the step
index. -/
def stepBond (ell : ℕ) (co : StepIdx ell → Cube ell) (μ : Fin 3)
    (t : PeriodicLatticeSite L × StepIdx ell) : Bond L :=
  (chart t.1 ell (co t.2), μ)

theorem stepBond_injOn (ell : ℕ) (hdvd : ∀ μ, ell ∣ (L μ + 1)) (μ : Fin 3)
    (co : StepIdx ell → Cube ell) (hco : Function.Injective co) :
    ∀ t ∈ (CoarseLattice L ell) ×ˢ (Finset.univ : Finset (StepIdx ell)),
      ∀ t' ∈ (CoarseLattice L ell) ×ˢ (Finset.univ : Finset (StepIdx ell)),
        stepBond ell co μ t = stepBond ell co μ t' → t = t' := by
  rintro ⟨y, j⟩ ht ⟨y', j'⟩ ht' h
  rw [Finset.mem_product] at ht ht'
  have hy : y ∈ CoarseLattice L ell := ht.1
  have hy' : y' ∈ CoarseLattice L ell := ht'.1
  have hs : chart y ell (co j) = chart y' ell (co j') := (Prod.ext_iff.mp h).1
  have hfit := coarseLattice_fits hdvd hy
  have hfit' := coarseLattice_fits hdvd hy'
  have hmem : chart y ell (co j) ∈ blockOf y ell := chart_mem_block hfit _
  have hmem' : chart y ell (co j) ∈ blockOf y' ell := by
    rw [hs]; exact chart_mem_block hfit' _
  have hyy : y = y' := coarseLattice_unique ell hy hy' hmem hmem'
  subst hyy
  have hj : j = j' := hco (chart_injective hfit hs)
  rw [hj]

theorem stepBond_image_disjoint (ell : ℕ) (co co' : StepIdx ell → Cube ell) {μ ν : Fin 3}
    (hne : μ ≠ ν) (A B : Finset (PeriodicLatticeSite L × StepIdx ell)) :
    Disjoint (Finset.image (stepBond ell co μ) A) (Finset.image (stepBond ell co' ν) B) := by
  rw [Finset.disjoint_left]
  rintro e he he'
  simp only [Finset.mem_image] at he he'
  obtain ⟨t, _, rfl⟩ := he
  obtain ⟨t', _, h⟩ := he'
  exact hne ((Prod.ext_iff.mp h).2).symm

theorem three_sets_sum_le (g : Bond L → ℝ) (hg : ∀ e, 0 ≤ g e) (S0 S1 S2 : Finset (Bond L))
    (h01 : Disjoint S0 S1) (h02 : Disjoint S0 S2) (h12 : Disjoint S1 S2) :
    ∑ e ∈ S0, g e + ∑ e ∈ S1, g e + ∑ e ∈ S2, g e ≤ ∑ e : Bond L, g e := by
  have hd : Disjoint (S0 ∪ S1) S2 := Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  rw [← Finset.sum_union h01, ← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => hg e)

/-- One direction's contribution, rewritten as a sum over a set of genuine lattice bonds. -/
theorem dir_sum_eq_image (lam : PeriodicLatticeSite L → ℝ) (ell : ℕ)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) (μ : Fin 3) (co : StepIdx ell → Cube ell)
    (hco : Function.Injective co) :
    ∑ t ∈ (CoarseLattice L ell) ×ˢ (Finset.univ : Finset (StepIdx ell)),
        (LatticeOperators.gradValue lam (stepBond ell co μ t)) ^ 2
      = ∑ e ∈ Finset.image (stepBond ell co μ)
          ((CoarseLattice L ell) ×ˢ (Finset.univ : Finset (StepIdx ell))),
          (LatticeOperators.gradValue lam e) ^ 2 := by
  rw [Finset.sum_image (stepBond_injOn ell hdvd μ co hco)]

/-- **THE SUPER-ADDITIVITY STEP**: the block-local (Neumann) energies, summed over the disjoint
block decomposition, are dominated by the ambient periodic Dirichlet form. -/
theorem block_energy_sum_le (lam : PeriodicLatticeSite L → ℝ) (ell : ℕ)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) :
    ∑ y ∈ CoarseLattice L ell,
        (cE0 ell (fun p => lam (chart y ell p)) + cE1 ell (fun p => lam (chart y ell p))
          + cE2 ell (fun p => lam (chart y ell p)))
      ≤ ∑ e : Bond L, (LatticeOperators.gradValue lam e) ^ 2 := by
  have hdir : ∀ (μ : Fin 3) (co co' : StepIdx ell → Cube ell),
      (∀ (y : PeriodicLatticeSite L), y ∈ CoarseLattice L ell → ∀ j : StepIdx ell,
        chart y ell (co' j) = periodicLatticeShift (chart y ell (co j)) μ) →
      ∀ y ∈ CoarseLattice L ell,
        (∑ j : StepIdx ell, (lam (chart y ell (co' j)) - lam (chart y ell (co j))) ^ 2)
          = ∑ j : StepIdx ell, (LatticeOperators.gradValue lam (stepBond ell co μ (y, j))) ^ 2 := by
    intro μ co co' hstep y hy
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hstep y hy j]
    rfl
  have hgrad0 := hdir 0 cubeOf0 cubeOf0'
    (fun y hy j => chart_step0 (coarseLattice_fits hdvd hy) j)
  have hgrad1 := hdir 1 cubeOf1 cubeOf1'
    (fun y hy j => chart_step1 (coarseLattice_fits hdvd hy) j)
  have hgrad2 := hdir 2 cubeOf2 cubeOf2'
    (fun y hy j => chart_step2 (coarseLattice_fits hdvd hy) j)
  have hsplit : ∀ (co : StepIdx ell → Cube ell) (μ : Fin 3)
      (hco : Function.Injective co)
      (F : PeriodicLatticeSite L → ℝ)
      (hF : ∀ y ∈ CoarseLattice L ell,
        F y = ∑ j : StepIdx ell, (LatticeOperators.gradValue lam (stepBond ell co μ (y, j))) ^ 2),
      ∑ y ∈ CoarseLattice L ell, F y
        = ∑ e ∈ Finset.image (stepBond ell co μ)
            ((CoarseLattice L ell) ×ˢ (Finset.univ : Finset (StepIdx ell))),
            (LatticeOperators.gradValue lam e) ^ 2 := by
    intro co μ hco F hF
    rw [Finset.sum_congr rfl hF, ← dir_sum_eq_image lam ell hdvd μ co hco,
      Finset.sum_product]
  have e0 := hsplit cubeOf0 0 cubeOf0_injective
    (fun y => cE0 ell (fun p => lam (chart y ell p)))
    (fun y hy => by rw [cE0_eq_stepIdx]; exact hgrad0 y hy)
  have e1 := hsplit cubeOf1 1 cubeOf1_injective
    (fun y => cE1 ell (fun p => lam (chart y ell p)))
    (fun y hy => by rw [cE1_eq_stepIdx]; exact hgrad1 y hy)
  have e2 := hsplit cubeOf2 2 cubeOf2_injective
    (fun y => cE2 ell (fun p => lam (chart y ell p)))
    (fun y hy => by rw [cE2_eq_stepIdx]; exact hgrad2 y hy)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e0, e1, e2]
  exact three_sets_sum_le (fun e => (LatticeOperators.gradValue lam e) ^ 2)
    (fun e => sq_nonneg _) _ _ _
    (stepBond_image_disjoint ell cubeOf0 cubeOf1 (by decide) _ _)
    (stepBond_image_disjoint ell cubeOf0 cubeOf2 (by decide) _ _)
    (stepBond_image_disjoint ell cubeOf1 cubeOf2 (by decide) _ _)

/-! ## §4. The lattice block Poincaré inequality -/

/-- **THE LATTICE BLOCK POINCARÉ INEQUALITY.** For a real function on the PERIODIC torus whose
average over every block of the coarse lattice `Λ' = CoarseLattice L ell` vanishes:

`∑_x λ(x)² ≤ (3·ell·(ell−1)/2) · ∑_bonds (∂₀λ)(b)²`.

The constant depends ONLY on the block side `ell` — never on the lattice extent `L`. The torus's
own spectral gap is never used; the local (Neumann) content enters solely through
`DiscretePoincare.discrete_poincare_crude` applied along coordinate lines INSIDE blocks. -/
theorem lattice_block_poincare (lam : PeriodicLatticeSite L → ℝ) (ell : ℕ) (hell : 1 ≤ ell)
    (hdvd : ∀ μ, ell ∣ (L μ + 1))
    (hker : ∀ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, lam x = 0) :
    ∑ x : PeriodicLatticeSite L, (lam x) ^ 2
      ≤ (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2)
        * ∑ e : Bond L, (LatticeOperators.gradValue lam e) ^ 2 := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hK : (0 : ℝ) ≤ 3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2 := by nlinarith
  rw [sum_eq_blocks ell (by omega) hdvd]
  have hstep : ∀ y ∈ CoarseLattice L ell,
      ∑ x ∈ blockOf y ell, (lam x) ^ 2
        ≤ (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2)
          * (cE0 ell (fun p => lam (chart y ell p)) + cE1 ell (fun p => lam (chart y ell p))
              + cE2 ell (fun p => lam (chart y ell p))) := by
    intro y hy
    have hfit := coarseLattice_fits hdvd hy
    rw [sum_block_eq_cube hfit (fun x => (lam x) ^ 2)]
    have hmz : ∑ p : Cube ell, lam (chart y ell p) = 0 := by
      rw [← sum_block_eq_cube hfit lam]
      exact hker y hy
    exact cube_poincare ell hell (fun p => lam (chart y ell p)) hmz
  calc ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, (lam x) ^ 2
      ≤ ∑ y ∈ CoarseLattice L ell, (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2)
          * (cE0 ell (fun p => lam (chart y ell p)) + cE1 ell (fun p => lam (chart y ell p))
              + cE2 ell (fun p => lam (chart y ell p))) := Finset.sum_le_sum hstep
    _ = (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2) * ∑ y ∈ CoarseLattice L ell,
          (cE0 ell (fun p => lam (chart y ell p)) + cE1 ell (fun p => lam (chart y ell p))
            + cE2 ell (fun p => lam (chart y ell p))) := by rw [Finset.mul_sum]
    _ ≤ (3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2)
          * ∑ e : Bond L, (LatticeOperators.gradValue lam e) ^ 2 :=
        mul_le_mul_of_nonneg_left (block_energy_sum_le lam ell hdvd) hK

/-! ## §5. The Hilbert-space bridge: `⟨v, Δ₀ v⟩` and `‖v‖²` as explicit lattice sums -/

theorem euclid_norm_sq {ι : Type*} [Fintype ι] (w : EuclideanSpace ℝ ι) :
    ‖w‖ ^ 2 = ∑ i, (w i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  simp [sq_abs]

theorem siteEquiv_apply (v : LatticeOperators.SiteSpace L) (x : PeriodicLatticeSite L) :
    LatticeOperators.siteEquiv L v x = v x := rfl

theorem bondEquiv_apply (w : LatticeOperators.BondSpace L) (e : Bond L) :
    LatticeOperators.bondEquiv L w e = w e := rfl

/-- `⟨v, Δ₀ v⟩ = ‖∂₀ v‖²`, the `Δ = ∂*∂` identity for the SITE Laplacian (the exact analogue of
`LatticeOperators.bondLaplacian_eq_curl_normSq` at the site level). -/
theorem inner_siteLaplacian_eq_grad_normSq (v : LatticeOperators.SiteSpace L) :
    (inner ℝ v (LatticeOperators.siteLaplacianCLM L v) : ℝ) = ‖LatticeOperators.gradCLM L v‖ ^ 2 := by
  unfold LatticeOperators.siteLaplacianCLM
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  simp

/-- `⟨v, Δ₀ v⟩` as an explicit sum of squared lattice differences. -/
theorem inner_siteLaplacian_eq_sum (v : LatticeOperators.SiteSpace L) :
    (inner ℝ v (LatticeOperators.siteLaplacianCLM L v) : ℝ)
      = ∑ e : Bond L, (LatticeOperators.gradValue (LatticeOperators.siteEquiv L v) e) ^ 2 := by
  rw [inner_siteLaplacian_eq_grad_normSq, euclid_norm_sq]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← bondEquiv_apply (LatticeOperators.gradCLM L v) e, LatticeOperators.gradCLM_apply]

/-- `‖v‖²` as an explicit sum of squares. -/
theorem norm_sq_eq_sum (v : LatticeOperators.SiteSpace L) :
    ‖v‖ ^ 2 = ∑ x : PeriodicLatticeSite L, (LatticeOperators.siteEquiv L v x) ^ 2 :=
  euclid_norm_sq v

/-! ## §6. THE BRIDGE: `positive_of_poincare`'s hypothesis, discharged -/

/-- Membership in `N(Q')` at a single coarse level is exactly "every block average vanishes". -/
theorem block_sum_zero_of_mem (ell : ℕ) (hell : 1 ≤ ell)
    (lam : PeriodicLatticeSite L → ℝ)
    (hlam : lam ∈ KernelSubspace.kernelSubspace [((ell, CoarseLattice L ell) : KernelSubspace.Level L)]) :
    ∀ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, lam x = 0 := by
  intro y hy
  have h := (KernelSubspace.mem_kernelSubspace).mp hlam (ell, CoarseLattice L ell) (by simp) y hy
  unfold KernelSubspace.coarseRestrictSite at h
  have hne : (1 / (ell : ℝ) ^ 3) ≠ 0 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  exact (mul_eq_zero.mp h).resolve_left hne

/-- **THE DELIVERED BOUND.** `positive_of_poincare`'s hypothesis `hbound`, for the single-level
kernel `N(Q') = {λ : Q'_ell λ = 0 on the whole coarse lattice Λ'}`, with the EXPLICIT constant

    c = 2 / (3·ell·(ell−1)).

Traceability: `2/(3·ell·(ell−1))` is the reciprocal of `cube_poincare`'s `3·ell·(ell−1)/2`, whose
factors are `3` (coordinate directions) and `ell(ell−1)/2` (`discrete_poincare_crude`'s own 1-D
constant). It depends ONLY on the block side `ell`, NOT on the lattice extent `L` — the periodic
torus's own gap plays no role. -/
theorem poincare_bound_on_coarse_kernel (ell : ℕ) (hell : 2 ≤ ell)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) :
    ∀ v : LatticeOperators.SiteSpace L,
      v ∈ KernelSubspace.kernelSubspaceH
          [((ell, CoarseLattice L ell) : KernelSubspace.Level L)] →
        (2 / (3 * (ell : ℝ) * ((ell : ℝ) - 1))) * ‖v‖ ^ 2
          ≤ (inner ℝ v (LatticeOperators.siteLaplacianCLM L v) : ℝ) := by
  intro v hv
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hKpos : (0 : ℝ) < 3 * (ell : ℝ) * ((ell : ℝ) - 1) / 2 := by nlinarith
  set lam := LatticeOperators.siteEquiv L v with hlamdef
  have hmem : lam ∈ KernelSubspace.kernelSubspace
      [((ell, CoarseLattice L ell) : KernelSubspace.Level L)] :=
    (KernelSubspace.mem_kernelSubspaceH).mp hv
  have hmain := lattice_block_poincare lam ell (by omega) hdvd
    (block_sum_zero_of_mem ell (by omega) lam hmem)
  rw [norm_sq_eq_sum, inner_siteLaplacian_eq_sum]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by nlinarith : (0:ℝ) < 3 * (ell : ℝ) * ((ell : ℝ) - 1))]
  nlinarith [hmain, Finset.sum_nonneg (fun (e : Bond L) (_ : e ∈ Finset.univ) =>
    sq_nonneg (LatticeOperators.gradValue lam e))]

/-- **THE CONSUMER, DISCHARGED.** `KernelSubspace.positive_of_poincare` applied with the constant
this file proves — `Δ₀` is genuinely positive on `N(Q')` for the single-level coarse kernel, with
no hypothesis left carried. -/
theorem siteLaplacian_positive_on_coarse_kernel (ell : ℕ) (hell : 2 ≤ ell)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) (v : LatticeOperators.SiteSpace L)
    (hv : v ∈ KernelSubspace.kernelSubspaceH
      [((ell, CoarseLattice L ell) : KernelSubspace.Level L)]) (hv0 : v ≠ 0) :
    0 < (inner ℝ v (LatticeOperators.siteLaplacianCLM L v) : ℝ) := by
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  refine KernelSubspace.positive_of_poincare _ (2 / (3 * (ell : ℝ) * ((ell : ℝ) - 1))) ?_
    (poincare_bound_on_coarse_kernel ell hell hdvd) v hv hv0
  have : (0 : ℝ) < 3 * (ell : ℝ) * ((ell : ℝ) - 1) := by nlinarith
  positivity

/-- **`Δ₀` is injective on `N(Q')`** — CMP96 p.225's own stated consequence ("positive... hence
invertible on this subspace"), now with NO carried hypothesis. -/
theorem eq_zero_of_siteLaplacian_eq_zero_on_coarse_kernel (ell : ℕ) (hell : 2 ≤ ell)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) (v : LatticeOperators.SiteSpace L)
    (hv : v ∈ KernelSubspace.kernelSubspaceH
      [((ell, CoarseLattice L ell) : KernelSubspace.Level L)])
    (hzero : LatticeOperators.siteLaplacianCLM L v = 0) : v = 0 := by
  by_contra hne
  have hpos := siteLaplacian_positive_on_coarse_kernel ell hell hdvd v hv hne
  rw [hzero, inner_zero_right] at hpos
  exact absurd hpos (lt_irrefl 0)

#print axioms cube_poincare
#print axioms lattice_block_poincare
#print axioms poincare_bound_on_coarse_kernel
#print axioms siteLaplacian_positive_on_coarse_kernel
#print axioms eq_zero_of_siteLaplacian_eq_zero_on_coarse_kernel


/-! ### §6b. Monotonicity in the level list — the bridge applies to any MULTI-SCALE `N(Q')`
containing a full coarse tiling at some scale.

CMP96 (2.7)/(2.10)'s `N(Q')` is a JOINT kernel over levels `j = 0,…,k`. Imposing MORE conditions
only SHRINKS the subspace, so the bound proved above for the single level
`(ell, CoarseLattice L ell)` transfers verbatim to every level list containing that level. -/

theorem kernelSubspace_mono {levels : List (KernelSubspace.Level L)}
    {lvl : KernelSubspace.Level L} (hlvl : lvl ∈ levels)
    {lam : PeriodicLatticeSite L → ℝ} (h : lam ∈ KernelSubspace.kernelSubspace levels) :
    lam ∈ KernelSubspace.kernelSubspace [lvl] := by
  rw [KernelSubspace.mem_kernelSubspace] at h ⊢
  intro l hl y hy
  simp only [List.mem_singleton] at hl
  subst hl
  exact h l hlvl y hy

theorem kernelSubspaceH_mono {levels : List (KernelSubspace.Level L)}
    {lvl : KernelSubspace.Level L} (hlvl : lvl ∈ levels)
    {v : LatticeOperators.SiteSpace L} (h : v ∈ KernelSubspace.kernelSubspaceH levels) :
    v ∈ KernelSubspace.kernelSubspaceH [lvl] := by
  rw [KernelSubspace.mem_kernelSubspaceH] at h ⊢
  exact kernelSubspace_mono hlvl h

/-- **The bridge, for an arbitrary multi-scale level list** containing a full coarse tiling at
block side `ell`. Same constant `2/(3·ell·(ell−1))`. -/
theorem poincare_bound_on_multiscale_kernel (ell : ℕ) (hell : 2 ≤ ell)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    (hlvl : ((ell, CoarseLattice L ell) : KernelSubspace.Level L) ∈ levels) :
    ∀ v : LatticeOperators.SiteSpace L, v ∈ KernelSubspace.kernelSubspaceH levels →
      (2 / (3 * (ell : ℝ) * ((ell : ℝ) - 1))) * ‖v‖ ^ 2
        ≤ (inner ℝ v (LatticeOperators.siteLaplacianCLM L v) : ℝ) :=
  fun v hv => poincare_bound_on_coarse_kernel ell hell hdvd v (kernelSubspaceH_mono hlvl hv)

/-- **The consumer, discharged for an arbitrary multi-scale level list.** -/
theorem siteLaplacian_positive_on_multiscale_kernel (ell : ℕ) (hell : 2 ≤ ell)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    (hlvl : ((ell, CoarseLattice L ell) : KernelSubspace.Level L) ∈ levels)
    (v : LatticeOperators.SiteSpace L) (hv : v ∈ KernelSubspace.kernelSubspaceH levels)
    (hv0 : v ≠ 0) :
    0 < (inner ℝ v (LatticeOperators.siteLaplacianCLM L v) : ℝ) := by
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  refine KernelSubspace.positive_of_poincare _ (2 / (3 * (ell : ℝ) * ((ell : ℝ) - 1))) ?_
    (poincare_bound_on_multiscale_kernel ell hell hdvd levels hlvl) v hv hv0
  have : (0 : ℝ) < 3 * (ell : ℝ) * ((ell : ℝ) - 1) := by nlinarith

  positivity

#print axioms poincare_bound_on_multiscale_kernel
#print axioms siteLaplacian_positive_on_multiscale_kernel

/-! ## §7. L7 witnesses — the delivered bound is NOT vacuous, and the trap is NOT sprung -/

theorem mem_single_level {ell : ℕ} {lam : PeriodicLatticeSite L → ℝ}
    (h : ∀ y ∈ CoarseLattice L ell, KernelSubspace.coarseRestrictSite ell lam y = 0) :
    lam ∈ KernelSubspace.kernelSubspace
      [((ell, CoarseLattice L ell) : KernelSubspace.Level L)] := by
  rw [KernelSubspace.mem_kernelSubspace]
  intro lvl hlvl y hy
  simp only [List.mem_singleton] at hlvl
  subst hlvl
  exact h y hy

/-- On the witness lattice, only the origin block can contain `witnessY`. -/
theorem coarse_block_forces_witnessY {y : PeriodicLatticeSite AdmissibleSubspace.witnessL}
    (hx : AdmissibleSubspace.witnessY ∈ blockOf y AdmissibleSubspace.witnessEll) :
    y = AdmissibleSubspace.witnessY := by
  rw [mem_blockOf] at hx
  funext μ
  apply Fin.ext
  have h := hx μ
  have hw : (AdmissibleSubspace.witnessY μ).val = 0 := rfl
  rw [hw] at h
  show (y μ).val = 0
  have : AdmissibleSubspace.witnessEll = 2 := rfl
  omega

/-- ... and, because coarse corners have even coordinates, only the origin block can contain the
`(1,0,0)` witness site either. -/
theorem coarse_block_forces_witnessY' {y : PeriodicLatticeSite AdmissibleSubspace.witnessL}
    (hy : y ∈ CoarseLattice AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll)
    (hx : KernelSubspace.kernelWitnessSiteA ∈ blockOf y AdmissibleSubspace.witnessEll) :
    y = AdmissibleSubspace.witnessY := by
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf] at hx
  funext μ
  apply Fin.ext
  have h : (y μ).val ≤ (KernelSubspace.kernelWitnessSiteA μ).val
      ∧ (KernelSubspace.kernelWitnessSiteA μ).val < (y μ).val + 2 := hx μ
  have hm : (y μ).val % 2 = 0 := hy μ
  have hv : (KernelSubspace.kernelWitnessSiteA μ).val ≤ 1 := by
    unfold KernelSubspace.kernelWitnessSiteA
    split_ifs
    · exact Nat.le_of_eq rfl
    · exact Nat.zero_le 1
  show (y μ).val = 0
  omega

/-- Every block average of the witness configuration vanishes: the origin block by the explicit
`+1/−1` cancellation already proved in `KernelSubspace`, every other block because the
configuration is supported entirely inside the origin block. -/
theorem bridgeWitness_block_sum (y : PeriodicLatticeSite AdmissibleSubspace.witnessL)
    (hy : y ∈ CoarseLattice AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll) :
    ∑ x ∈ blockOf y AdmissibleSubspace.witnessEll, KernelSubspace.weakWitnessLam x = 0 := by
  by_cases hyw : y = AdmissibleSubspace.witnessY
  · subst hyw
    exact KernelSubspace.weakWitnessLam_block_sum_eq_zero
  · refine Finset.sum_eq_zero (fun x hx => ?_)
    have h1 : x ≠ AdmissibleSubspace.witnessY := by
      rintro rfl
      exact hyw (coarse_block_forces_witnessY hx)
    have h2 : x ≠ KernelSubspace.kernelWitnessSiteA := by
      rintro rfl
      exact hyw (coarse_block_forces_witnessY' hy hx)
    simp only [KernelSubspace.weakWitnessLam, if_neg h1, if_neg h2]

/-- The witness vector in the Hilbert space. -/
noncomputable def bridgeWitnessV : LatticeOperators.SiteSpace AdmissibleSubspace.witnessL :=
  (LatticeOperators.siteEquiv AdmissibleSubspace.witnessL).symm KernelSubspace.weakWitnessLam

theorem bridgeWitnessV_equiv :
    LatticeOperators.siteEquiv AdmissibleSubspace.witnessL bridgeWitnessV
      = KernelSubspace.weakWitnessLam := by
  unfold bridgeWitnessV
  exact LinearEquiv.apply_symm_apply _ _

/-- **L7: the kernel is genuinely inhabited by a NONZERO vector**, so the delivered bound and the
positivity corollary below are not vacuous. -/
theorem bridgeWitnessV_mem :
    bridgeWitnessV ∈ KernelSubspace.kernelSubspaceH
      [((AdmissibleSubspace.witnessEll,
          CoarseLattice AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll) :
            KernelSubspace.Level AdmissibleSubspace.witnessL)] := by
  rw [KernelSubspace.mem_kernelSubspaceH, bridgeWitnessV_equiv]
  refine mem_single_level (fun y hy => ?_)
  unfold KernelSubspace.coarseRestrictSite
  rw [bridgeWitness_block_sum y hy, mul_zero]

theorem bridgeWitnessV_ne_zero : bridgeWitnessV ≠ 0 := by
  intro h
  have hc := congrArg (LatticeOperators.siteEquiv AdmissibleSubspace.witnessL) h
  rw [bridgeWitnessV_equiv, map_zero] at hc
  have hy := congrFun hc AdmissibleSubspace.witnessY
  rw [KernelSubspace.weakWitnessLam_at_witnessY] at hy
  norm_num at hy

/-- **The full chain, at a concrete instance**: `Δ₀` is strictly positive on a concrete NONZERO
element of `N(Q')` on the witness lattice — nothing here is vacuous. -/
theorem bridgeWitnessV_laplacian_positive :
    0 < (inner ℝ bridgeWitnessV (LatticeOperators.siteLaplacianCLM
      AdmissibleSubspace.witnessL bridgeWitnessV) : ℝ) :=
  siteLaplacian_positive_on_coarse_kernel AdmissibleSubspace.witnessEll (by decide) (by decide)
    bridgeWitnessV bridgeWitnessV_mem bridgeWitnessV_ne_zero

/-! ### §7b. D4 — the kernel hypothesis is load-bearing -/

theorem coarseRestrictSite_const_witness :
    KernelSubspace.coarseRestrictSite AdmissibleSubspace.witnessEll
      (fun _ => (1 : ℝ)) AdmissibleSubspace.witnessY = 1 := by
  unfold KernelSubspace.coarseRestrictSite
  rw [Finset.sum_const, card_blockOf _ _ AdmissibleSubspace.witnessY_fits]
  norm_num [AdmissibleSubspace.witnessEll]

/-- **D4**: the constant function — the vector on which `Δ₀` genuinely FAILS to be positive
(`KernelSubspace.constSite_witness_laplacian_not_positive`) — is NOT in `N(Q')`. The kernel
membership hypothesis of the delivered bound is therefore load-bearing, not decorative. -/
theorem constSite_not_mem_coarse_kernel :
    KernelSubspace.constSite AdmissibleSubspace.witnessL (1 : ℝ) ∉
      KernelSubspace.kernelSubspaceH
        [((AdmissibleSubspace.witnessEll,
            CoarseLattice AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll) :
              KernelSubspace.Level AdmissibleSubspace.witnessL)] := by
  intro hmem
  rw [KernelSubspace.mem_kernelSubspaceH, KernelSubspace.siteEquiv_constSite] at hmem
  have h := (KernelSubspace.mem_kernelSubspace).mp hmem
    (AdmissibleSubspace.witnessEll,
      CoarseLattice AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll)
    (by simp) AdmissibleSubspace.witnessY AdmissibleSubspace.witnessY_coarse
  rw [coarseRestrictSite_const_witness] at h
  norm_num at h

/-! ### §7c. THE TRAP CHECK — the constant is a function of the BLOCK SIDE, not the lattice extent

The mandate's trap: a periodic-torus Laplacian has physical gap `4π²/N²`-shaped, i.e. a constant
that SHRINKS as the lattice grows. The constant delivered here is `2/(3·ell·(ell−1))`; it contains
no `L` at all. Instantiated at the SAME block side `ell = 2` on two lattices of DIFFERENT extent
(4 and 8 sites per coordinate) it is literally the SAME number `1/3`. A torus-gap-derived constant
could not be. -/
theorem bridge_constant_extent_independent :
    (∀ v : LatticeOperators.SiteSpace (fun _ => 3),
        v ∈ KernelSubspace.kernelSubspaceH
            [((2, CoarseLattice (fun _ => 3) 2) : KernelSubspace.Level (fun _ => 3))] →
          (1 / 3 : ℝ) * ‖v‖ ^ 2
            ≤ (inner ℝ v (LatticeOperators.siteLaplacianCLM (fun _ => 3) v) : ℝ))
    ∧ (∀ v : LatticeOperators.SiteSpace (fun _ => 7),
        v ∈ KernelSubspace.kernelSubspaceH
            [((2, CoarseLattice (fun _ => 7) 2) : KernelSubspace.Level (fun _ => 7))] →
          (1 / 3 : ℝ) * ‖v‖ ^ 2
            ≤ (inner ℝ v (LatticeOperators.siteLaplacianCLM (fun _ => 7) v) : ℝ)) := by
  constructor
  · intro v hv
    have h := poincare_bound_on_coarse_kernel (L := fun _ => 3) 2 (by norm_num) (by decide) v hv
    norm_num at h
    linarith
  · intro v hv
    have h := poincare_bound_on_coarse_kernel (L := fun _ => 7) 2 (by norm_num) (by decide) v hv
    norm_num at h
    linarith

#print axioms bridgeWitnessV_mem
#print axioms bridgeWitnessV_ne_zero
#print axioms bridgeWitnessV_laplacian_positive
#print axioms constSite_not_mem_coarse_kernel
#print axioms bridge_constant_extent_independent


end AdalyFormal.Balaban.PoincareBridge
