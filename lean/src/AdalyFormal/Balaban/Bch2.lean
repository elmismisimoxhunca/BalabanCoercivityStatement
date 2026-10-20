/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ClassPropagationUbar
import AdalyFormal.Balaban.RegularityGap

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# BCH-2 AT `su(2)`: the quadratic remainder of `log(exp A · exp B)`

Lane record: `compute/bch2/PROGRESS.md`.
-/

namespace AdalyFormal.Balaban.Bch2

open Matrix
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.RegularityGap (Yof Y_sq su2Log_eq_kappa_smul su2_trace_eq
  su2_add_conjTranspose real_smul_eq frobNorm_neg frobNorm_sub_le)

open scoped Matrix

/-! ## §1 — `su(2)`, its real inner product, and the two algebraic brick lemmas -/

/-- Membership in `𝔰𝔲(2)`: traceless anti-Hermitian. -/
def IsSu2 (X : M2) : Prop := Xᴴ = -X ∧ Matrix.trace X = 0

/-- `ν X = √(frobSq X / 2)`. On `𝔰𝔲(2)` this is the `ℝ³` (rotation-vector) length: `X² = −(ν X)²·1`
and `‖X‖_F = √2 · ν X`. -/
noncomputable def nu (X : M2) : ℝ := Real.sqrt (frobSq X / 2)

/-- The REAL Frobenius inner product `Re Σ conj(Xᵢⱼ)·Yᵢⱼ`, written on the four entries so that
every bilinearity fact below is a `ring` identity. Normalised so that `ip X X = frobSq X`. -/
noncomputable def ip (X Y : M2) : ℝ :=
  ((X 0 0).re * (Y 0 0).re + (X 0 0).im * (Y 0 0).im)
  + ((X 0 1).re * (Y 0 1).re + (X 0 1).im * (Y 0 1).im)
  + ((X 1 0).re * (Y 1 0).re + (X 1 0).im * (Y 1 0).im)
  + ((X 1 1).re * (Y 1 1).re + (X 1 1).im * (Y 1 1).im)

/-- Real scalars pass through `ᴴ` unconjugated. Proved entrywise so it does not depend on which
of Mathlib's several `conjTranspose_smul` forms this pin carries. -/
theorem conjT_real_smul (r : ℝ) (M : M2) : (((r : ℝ) : ℂ) • M)ᴴ = ((r : ℝ) : ℂ) • Mᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.smul_apply, Complex.conj_ofReal]

theorem ip_self (X : M2) : ip X X = frobSq X := by
  simp only [ip, frobSq, Complex.normSq_apply]

theorem ip_comm (X Y : M2) : ip X Y = ip Y X := by simp only [ip]; ring

theorem frobSq_add (X Y : M2) : frobSq (X + Y) = frobSq X + 2 * ip X Y + frobSq Y := by
  simp only [frobSq, ip, Complex.normSq_apply, Matrix.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem frobSq_sub (X Y : M2) : frobSq (X - Y) = frobSq X - 2 * ip X Y + frobSq Y := by
  simp only [frobSq, ip, Complex.normSq_apply, Matrix.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem ip_smul_left (r : ℝ) (X Y : M2) : ip (r • X) Y = r * ip X Y := by
  simp only [ip, Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem ip_smul_right (r : ℝ) (X Y : M2) : ip X (r • Y) = r * ip X Y := by
  rw [ip_comm, ip_smul_left, ip_comm]

theorem frobSq_smul (r : ℝ) (X : M2) : frobSq (r • X) = r ^ 2 * frobSq X := by
  rw [← ip_self, ← ip_self, ip_smul_left, ip_smul_right]; ring

/-! ### `ν` and `frobNorm` -/

theorem nu_nonneg (X : M2) : 0 ≤ nu X := Real.sqrt_nonneg _

theorem nu_sq (X : M2) : nu X ^ 2 = frobSq X / 2 :=
  Real.sq_sqrt (by have := frobSq_nonneg X; linarith)

theorem frobNorm_eq_sqrt_two_mul_nu (X : M2) : frobNorm X = Real.sqrt 2 * nu X := by
  unfold frobNorm nu
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1
  have := frobSq_nonneg X
  field_simp

theorem nu_eq_zero_iff (X : M2) : nu X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have h2 := nu_sq X
    rw [h] at h2
    exact AdalyFormal.Balaban.AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero (by linarith)
  · intro h; subst h; simp [nu, frobSq]

theorem nu_smul (r : ℝ) (X : M2) : nu (r • X) = |r| * nu X := by
  unfold nu
  rw [frobSq_smul]
  have h : r ^ 2 * frobSq X / 2 = r ^ 2 * (frobSq X / 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

theorem nu_neg (X : M2) : nu (-X) = nu X := by
  have h : (-X) = ((-1 : ℝ)) • X := by module
  rw [h, nu_smul]; norm_num

theorem nu_add_le (X Y : M2) : nu (X + Y) ≤ nu X + nu Y := by
  have h := frobNorm_sub_le X (-Y)
  rw [sub_neg_eq_add, frobNorm_neg] at h
  rw [frobNorm_eq_sqrt_two_mul_nu, frobNorm_eq_sqrt_two_mul_nu,
    frobNorm_eq_sqrt_two_mul_nu] at h
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h]

/-! ### `IsSu2` is a real subspace closed under the commutator -/

theorem IsSu2.add {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) : IsSu2 (X + Y) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_add, hX.1, hY.1]; module
  · rw [Matrix.trace_add, hX.2, hY.2]; ring

theorem IsSu2.smul {X : M2} (hX : IsSu2 X) (r : ℝ) : IsSu2 (r • X) := by
  refine ⟨?_, ?_⟩
  · rw [← real_smul_eq r X, conjT_real_smul, hX.1, real_smul_eq]
    module
  · rw [← real_smul_eq r X, Matrix.trace_smul, hX.2]; simp

theorem IsSu2.neg {X : M2} (hX : IsSu2 X) : IsSu2 (-X) := by
  have h : (-X) = ((-1 : ℝ)) • X := by module
  rw [h]; exact hX.smul (-1)

theorem IsSu2.sub {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) : IsSu2 (X - Y) := by
  rw [sub_eq_add_neg]; exact hX.add hY.neg

theorem IsSu2.zero : IsSu2 (0 : M2) := ⟨by simp, by simp⟩

/-- **CAYLEY–HAMILTON, in `ν`-form.** `X² = −(ν X)²·1` for `X ∈ 𝔰𝔲(2)`. -/
theorem sq_eq {X : M2} (hX : IsSu2 X) : X * X = ((-(nu X ^ 2) : ℝ) : ℂ) • (1 : M2) := by
  rw [AdalyFormal.Balaban.ClassPropagationUbar.alg_sq hX.1 hX.2, nu_sq]

/-- Scalars are read off the `(0,0)` entry, so `a•1 = b•1 → a = b`. -/
theorem smul_one_inj {a b : ℝ} (h : ((a : ℝ) : ℂ) • (1 : M2) = ((b : ℝ) : ℂ) • (1 : M2)) :
    a = b := by
  have h2 := congrFun (congrFun h 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  exact_mod_cast h2

/-- **THE ANTICOMMUTATOR IS A SCALAR.** `XY + YX = −ip(X,Y)·1` on `𝔰𝔲(2)`. -/
theorem anticomm {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) :
    X * Y + Y * X = ((-(ip X Y) : ℝ) : ℂ) • (1 : M2) := by
  have hXY := sq_eq (hX.add hY)
  have hXX := sq_eq hX
  have hYY := sq_eq hY
  have hexp : (X + Y) * (X + Y) = X * X + (X * Y + Y * X) + Y * Y := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]; abel
  have hn : nu (X + Y) ^ 2 = nu X ^ 2 + ip X Y + nu Y ^ 2 := by
    rw [nu_sq, nu_sq, nu_sq, frobSq_add]; ring
  rw [hexp, hXX, hYY, hn] at hXY
  have hsub : (X * Y + Y * X)
      = ((-(nu X ^ 2 + ip X Y + nu Y ^ 2) : ℝ) : ℂ) • (1 : M2)
        - ((-(nu X ^ 2) : ℝ) : ℂ) • (1 : M2) - ((-(nu Y ^ 2) : ℝ) : ℂ) • (1 : M2) := by
    rw [← hXY]; abel
  rw [hsub]
  push_cast
  module

/-- Half the commutator, `C = ½(XY − YX)`. -/
noncomputable def comm2 (X Y : M2) : M2 := ((1/2 : ℝ) : ℂ) • (X * Y - Y * X)

theorem IsSu2.comm2 {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) : IsSu2 (Bch2.comm2 X Y) := by
  refine ⟨?_, ?_⟩
  · rw [Bch2.comm2, conjT_real_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX.1, hY.1,
      show (-Y) * (-X) = Y * X by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg],
      show (-X) * (-Y) = X * Y by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg]]
    module
  · rw [Bch2.comm2, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm X Y]
    simp

/-- `XY = −½ip(X,Y)·1 + C`. -/
theorem mul_eq {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) :
    X * Y = ((-(ip X Y) / 2 : ℝ) : ℂ) • (1 : M2) + comm2 X Y := by
  have h := anticomm hX hY
  have e : X * Y - comm2 X Y = ((1/2 : ℝ) : ℂ) • (X * Y + Y * X) := by
    rw [comm2]; push_cast; module
  rw [h, smul_smul] at e
  have e2 : X * Y - comm2 X Y = ((-(ip X Y) / 2 : ℝ) : ℂ) • (1 : M2) := by
    rw [e]; congr 1; push_cast; ring
  exact sub_eq_iff_eq_add.mp e2

/-- The `(a•1 + C)(a•1 − C) = a²•1 − C²` expansion, isolated because central scalars need it
spelled out for matrices. -/
theorem central_expand (a : ℂ) (C : M2) :
    (a • (1 : M2) + C) * (a • (1 : M2) - C) = (a * a) • (1 : M2) - C * C := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  module

/-- **THE ALGEBRAIC BRICK.** `(ν C)² = (ν X)²(ν Y)² − (ip/2)²` for `C = ½[X,Y]` on `𝔰𝔲(2)`.

This ONE identity yields both facts the estimate needs — Cauchy–Schwarz `|ip| ≤ 2 ν_X ν_Y`
(because `(ν C)² ≥ 0`) and the commutator bound `ν C ≤ ν_X ν_Y` (because `(ip/2)² ≥ 0`). No
separate Cauchy–Schwarz argument, and no submultiplicativity of the Frobenius norm, is used
anywhere in this file. -/
theorem nu_comm2_sq {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) :
    nu (comm2 X Y) ^ 2 = nu X ^ 2 * nu Y ^ 2 - (ip X Y / 2) ^ 2 := by
  have hXsq := sq_eq hX
  have hYsq := sq_eq hY
  have hPQ : (X * Y) * (Y * X) = ((nu X ^ 2 * nu Y ^ 2 : ℝ) : ℂ) • (1 : M2) := by
    have e1 : (X * Y) * (Y * X) = X * ((Y * Y) * X) := by simp only [Matrix.mul_assoc]
    rw [e1, hYsq, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hXsq, smul_smul]
    push_cast
    module
  have hP : X * Y = ((-(ip X Y) / 2 : ℝ) : ℂ) • (1 : M2) + comm2 X Y := mul_eq hX hY
  have hQ : Y * X = ((-(ip X Y) / 2 : ℝ) : ℂ) • (1 : M2) - comm2 X Y := by
    have h := anticomm hX hY
    have h2 : Y * X = ((-(ip X Y) : ℝ) : ℂ) • (1 : M2) - X * Y := by rw [← h]; abel
    rw [h2, hP]; push_cast; module
  rw [hP, hQ, central_expand, sq_eq (hX.comm2 hY)] at hPQ
  have key : (((ip X Y / 2) ^ 2 + nu (comm2 X Y) ^ 2 : ℝ) : ℂ) • (1 : M2)
      = ((nu X ^ 2 * nu Y ^ 2 : ℝ) : ℂ) • (1 : M2) := by
    rw [← hPQ]; push_cast; module
  have := smul_one_inj key
  linarith

/-- From `a² ≤ b²` and `0 ≤ b`, `|a| ≤ b`. -/
theorem abs_le_of_sq_le_sq' {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  nlinarith [abs_nonneg a, sq_abs a]

/-- **CAUCHY–SCHWARZ on `𝔰𝔲(2)`, for free.** -/
theorem abs_ip_le {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) :
    |ip X Y| ≤ 2 * (nu X * nu Y) := by
  have h := nu_comm2_sq hX hY
  have h0 : (0:ℝ) ≤ nu (comm2 X Y) ^ 2 := sq_nonneg _
  have hle : (ip X Y) ^ 2 ≤ (2 * (nu X * nu Y)) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hle
    (mul_nonneg (by norm_num) (mul_nonneg (nu_nonneg X) (nu_nonneg Y)))

/-- **THE COMMUTATOR BOUND.** `ν(½[X,Y]) ≤ ν X · ν Y`. -/
theorem nu_comm2_le {X Y : M2} (hX : IsSu2 X) (hY : IsSu2 Y) :
    nu (comm2 X Y) ≤ nu X * nu Y := by
  have h := nu_comm2_sq hX hY
  have h1 : nu (comm2 X Y) ^ 2 ≤ (nu X * nu Y) ^ 2 := by nlinarith [sq_nonneg (ip X Y / 2)]
  have h2 := abs_le_of_sq_le_sq' h1 (mul_nonneg (nu_nonneg X) (nu_nonneg Y))
  rwa [abs_of_nonneg (nu_nonneg _)] at h2

/-! ## §2 — The `SU(2)` decomposition `g = cos θ · 1 + W`, `W ∈ 𝔰𝔲(2)`, `ν W = sin θ` -/

open AdalyFormal.Balaban.BlockingLinkEstimate (cos_su2Angle sin_su2Angle_nonneg)

theorem su2Angle_nonneg (g : SU2) : 0 ≤ su2Angle g := Real.arccos_nonneg _

theorem su2Angle_le_pi (g : SU2) : su2Angle g ≤ Real.pi := Real.arccos_le_pi _

/-- `g = cos θ · 1 + Yof g` — this is `Yof`'s definition, restated with a real `•`. -/
theorem su2_decomp (g : SU2) :
    (g : M2) = (Real.cos (su2Angle g)) • (1 : M2) + Yof g := by
  rw [Yof, real_smul_eq]
  abel

theorem isSu2_Yof (g : SU2) : IsSu2 (Yof g) := by
  have htr : Matrix.trace (g : M2) = ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) := su2_trace_eq g
  refine ⟨?_, ?_⟩
  · have hgH : (g : M2)ᴴ = ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) • (1 : M2) - (g : M2) := by
      have h := su2_add_conjTranspose g
      rw [htr] at h
      rw [← h]; abel
    rw [Yof, Matrix.conjTranspose_sub, conjT_real_smul, Matrix.conjTranspose_one, hgH]
    push_cast
    module
  · rw [Yof, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, htr]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring

/-- **`ν(Yof g) = sin θ(g)`.** -/
theorem nu_Yof (g : SU2) : nu (Yof g) = Real.sin (su2Angle g) := by
  have h1 := Y_sq g
  have h2 := sq_eq (isSu2_Yof g)
  rw [h1] at h2
  have h3 : -Real.sin (su2Angle g) ^ 2 = -(nu (Yof g) ^ 2) := smul_one_inj h2
  have h4 : nu (Yof g) ^ 2 = Real.sin (su2Angle g) ^ 2 := by linarith
  have h5 := abs_le_of_sq_le_sq' (le_of_eq h4) (sin_su2Angle_nonneg g)
  have h6 := abs_le_of_sq_le_sq' (le_of_eq h4.symm) (nu_nonneg (Yof g))
  rw [abs_of_nonneg (nu_nonneg _)] at h5
  rw [abs_of_nonneg (sin_su2Angle_nonneg g)] at h6
  linarith

/-! ### `κ` on the cap `θ ≤ π/2` -/

theorem kappa_nonneg (g : SU2) : 0 ≤ su2Kappa g :=
  div_nonneg (su2Angle_nonneg g) (sin_su2Angle_nonneg g)

theorem kappa_mul_sin {g : SU2} (h : su2Angle g ≤ Real.pi / 2) :
    su2Kappa g * Real.sin (su2Angle g) = su2Angle g := by
  rcases eq_or_lt_of_le (su2Angle_nonneg g) with h0 | h0
  · rw [← h0]; simp [su2Kappa, ← h0]
  · have hs : 0 < Real.sin (su2Angle g) :=
      Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    rw [su2Kappa]
    field_simp

theorem kappa_le {g : SU2} (h : su2Angle g ≤ Real.pi / 2) : su2Kappa g ≤ Real.pi / 2 := by
  rcases eq_or_lt_of_le (su2Angle_nonneg g) with h0 | h0
  · rw [su2Kappa, ← h0]; simp; positivity
  · have hs : 0 < Real.sin (su2Angle g) :=
      Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hj := Real.mul_le_sin (le_of_lt h0) h
    have hpi := Real.pi_pos
    rw [su2Kappa, div_le_iff₀ hs]
    have h2 : (Real.pi / 2) * (2 / Real.pi * su2Angle g)
        ≤ (Real.pi / 2) * Real.sin (su2Angle g) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    have h3 : (Real.pi / 2) * (2 / Real.pi * su2Angle g) = su2Angle g := by
      field_simp
    linarith

/-! ## §3 — LEMMA L: `su2Log` is `(π/2)`-Lipschitz on the cap `θ ≤ π/2` -/

theorem frobNorm_le_of_frobSq_le {c : ℝ} (hc : 0 ≤ c) {A B : M2}
    (h : frobSq A ≤ c ^ 2 * frobSq B) : frobNorm A ≤ c * frobNorm B := by
  unfold frobNorm
  calc Real.sqrt (frobSq A) ≤ Real.sqrt (c ^ 2 * frobSq B) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt (frobSq B) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **JORDAN, squared and two-sided.** `d² ≤ π²·sin²(d/2)` for `|d| ≤ π/2`. -/
theorem jordan_sq {d : ℝ} (h : |d| ≤ Real.pi / 2) :
    d ^ 2 ≤ Real.pi ^ 2 * Real.sin (d / 2) ^ 2 := by
  have hpi := Real.pi_pos
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 → x ^ 2 ≤ Real.pi ^ 2 * Real.sin (x / 2) ^ 2 := by
    intro x hx0 hx
    have hj := Real.mul_le_sin (x := x / 2) (by linarith) (by linarith)
    have hs : 0 ≤ Real.sin (x / 2) := le_trans (by positivity) hj
    have heq : 2 / Real.pi * (x / 2) = x / Real.pi := by field_simp
    rw [heq] at hj
    have hx' : (0:ℝ) ≤ x / Real.pi := by positivity
    have h4 : (x / Real.pi) ^ 2 ≤ Real.sin (x / 2) ^ 2 := by nlinarith [hj, hx', hs]
    have h5 : (x / Real.pi) ^ 2 = x ^ 2 / Real.pi ^ 2 := by field_simp
    rw [h5, div_le_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 2)] at h4
    linarith
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd] at h
    exact key d hd h
  · rw [abs_of_nonpos hd] at h
    have := key (-d) (by linarith) h
    have hsin : Real.sin (-d / 2) = -Real.sin (d / 2) := by
      rw [show (-d / 2 : ℝ) = -(d / 2) by ring, Real.sin_neg]
    rw [hsin] at this
    nlinarith [this]

/-- **LEMMA L.** `‖log g − log g'‖_F ≤ (π/2)·‖g − g'‖_F` whenever both angles are `≤ π/2`.

**The constant `π/2` is SHARP — and as of 2026-08-03 that word is carried by a KERNEL THEOREM,
not by numerics.** The canonical form is `su2Log_lipschitz_isLeast`: `π/2` is the LEAST real `c`
for which this very statement holds. It is proved from an EQUALITY, not from a limit: on the cap
BOUNDARY `θ = π/2` one has `log g = (π/2)·g` exactly (`su2Log_eq_half_pi_smul`), so the inequality
is an EQUALITY for every boundary pair (`su2Log_lipschitz_attained_on_boundary`); at the pinned
separated pair `sG = exp((π/2)·J) = J`, `sG' = exp(−(π/2)·J) = −J` this reads
`π√2 = (π/2)·2√2` with both sides nonzero (`su2Log_lipschitz_attained`, `sharp_pair_separated`).
Hence no smaller constant works (`su2Log_lipschitz_constant_sharp`), and the `3/2` form in
particular is FALSE (`su2Log_not_lipschitz_three_halves`). Strictly INSIDE the cap the inequality
is STRICT (`lipschitz_strict_inside`, at `θ = π/4`), so this is a statement about the boundary and
not an identity in disguise. All of it is §9.

~~"The constant is SHARP: the two-sided ratio approaches `π/2` as `θ, θ' → π/2` with `W ∥ −W'`."~~
**STRUCK 2026-08-03**, gate-1 prosecution (`compute/bch2_prosecution/VERDICT.md`, ruling 4b
CONVICT). Two things were wrong with that sentence. (i) EVIDENCE: the only support anywhere in this
lane for the word SHARP was a Python random-sampling exploration, which signs nothing under the
REFORM CHARTER — the word was billed, not proved. (ii) CONTENT: "approaches" understated the truth.
The ratio is ATTAINED, on a whole 2-sphere of pairs, and `W ∥ −W'` is not needed — ANY two
boundary elements attain it, including the ORTHOGONAL pair `(J, K)`
(`su2Log_lipschitz_attained_orthogonal`, `orth_pair_separated`: `π = (π/2)·2`, both sides nonzero).

No case split on `g = 1` is needed — `su2Kappa 1 = 0/0 = 0` in Lean, and `κ·sin θ = θ` still
holds there because both sides are `0`. -/
theorem su2Log_lipschitz {g g' : SU2} (hg : su2Angle g ≤ Real.pi / 2)
    (hg' : su2Angle g' ≤ Real.pi / 2) :
    frobNorm (su2Log g - su2Log g') ≤ (Real.pi / 2) * frobNorm ((g : M2) - (g' : M2)) := by
  have hpi := Real.pi_pos
  set t := su2Angle g with ht
  set t' := su2Angle g' with ht'
  set W := Yof g with hW
  set W' := Yof g' with hW'
  set k := su2Kappa g with hk
  set k' := su2Kappa g' with hk'
  have hWs : IsSu2 W := isSu2_Yof g
  have hWs' : IsSu2 W' := isSu2_Yof g'
  have hnW : nu W = Real.sin t := nu_Yof g
  have hnW' : nu W' = Real.sin t' := nu_Yof g'
  have hks : k * Real.sin t = t := kappa_mul_sin hg
  have hks' : k' * Real.sin t' = t' := kappa_mul_sin hg'
  have hkn : 0 ≤ k := kappa_nonneg g
  have hkn' : 0 ≤ k' := kappa_nonneg g'
  have hkl : k ≤ Real.pi / 2 := kappa_le hg
  have hkl' : k' ≤ Real.pi / 2 := kappa_le hg'
  -- numerator
  have hlogdiff : su2Log g - su2Log g' = k • W - k' • W' := by
    rw [su2Log_eq_kappa_smul g, su2Log_eq_kappa_smul g', real_smul_eq, real_smul_eq]
  have hnum : frobSq (su2Log g - su2Log g')
      = 2 * (t ^ 2 + t' ^ 2 - k * k' * ip W W') := by
    rw [hlogdiff, frobSq_sub, frobSq_smul, frobSq_smul, ip_smul_left, ip_smul_right,
      ← ip_self W, ← ip_self W']
    have e1 : ip W W = 2 * Real.sin t ^ 2 := by
      rw [ip_self]
      have hq := nu_sq W; rw [hnW] at hq; linarith
    have e2 : ip W' W' = 2 * Real.sin t' ^ 2 := by
      rw [ip_self]
      have hq := nu_sq W'; rw [hnW'] at hq; linarith
    rw [e1, e2]
    nlinarith [hks, hks']
  -- denominator
  have hden : frobSq ((g : M2) - (g' : M2))
      = 2 * ((Real.cos t - Real.cos t') ^ 2 + Real.sin t ^ 2 + Real.sin t' ^ 2
        - ip W W') := by
    have hd : (g : M2) - (g' : M2) = (Real.cos t - Real.cos t') • (1 : M2) + (1:ℝ) • (W - W') := by
      rw [su2_decomp g, su2_decomp g', ← ht, ← ht', ← hW, ← hW', sub_smul, one_smul]
      abel
    rw [hd, AdalyFormal.Balaban.ClassPropagationUbar.comb_frobSq (hWs.sub hWs').1
      (hWs.sub hWs').2, frobSq_sub, ← ip_self W, ← ip_self W']
    have e1 : ip W W = 2 * Real.sin t ^ 2 := by
      rw [ip_self]
      have hq := nu_sq W; rw [hnW] at hq; linarith
    have e2 : ip W' W' = 2 * Real.sin t' ^ 2 := by
      rw [ip_self]
      have hq := nu_sq W'; rw [hnW'] at hq; linarith
    rw [e1, e2]
    ring
  -- the real inequality
  have hI : ip W W' ≤ 2 * (Real.sin t * Real.sin t') := by
    have := abs_ip_le hWs hWs'
    rw [hnW, hnW'] at this
    exact le_trans (le_abs_self _) this
  have hprod : k * k' * (Real.sin t * Real.sin t') = t * t' := by
    calc k * k' * (Real.sin t * Real.sin t') = (k * Real.sin t) * (k' * Real.sin t') := by ring
      _ = t * t' := by rw [hks, hks']
  have hkk : k * k' - Real.pi ^ 2 / 4 ≤ 0 := by nlinarith
  have hstep : 2 * (t * t') - Real.pi ^ 2 / 2 * (Real.sin t * Real.sin t')
      ≤ k * k' * ip W W' - Real.pi ^ 2 / 4 * ip W W' := by
    have h0 := mul_le_mul_of_nonpos_right hI hkk
    nlinarith [h0, hprod]
  have hcos : (Real.cos t - Real.cos t') ^ 2
      + (Real.sin t ^ 2 - 2 * (Real.sin t * Real.sin t') + Real.sin t' ^ 2)
      = 2 - 2 * Real.cos (t - t') := by
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq t']
  have hhalf : Real.cos (t - t') = 1 - 2 * Real.sin ((t - t') / 2) ^ 2 := by
    have h := Real.cos_two_mul ((t - t') / 2)
    rw [show 2 * ((t - t') / 2) = t - t' by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq ((t - t') / 2)]
  have hjor : (t - t') ^ 2 ≤ Real.pi ^ 2 * Real.sin ((t - t') / 2) ^ 2 := by
    refine jordan_sq ?_
    rw [abs_le]
    constructor <;> [linarith [su2Angle_nonneg g, su2Angle_nonneg g'];
      linarith [su2Angle_nonneg g, su2Angle_nonneg g']]
  have hkey : frobSq (su2Log g - su2Log g')
      ≤ (Real.pi / 2) ^ 2 * frobSq ((g : M2) - (g' : M2)) := by
    rw [hnum, hden]
    nlinarith [hstep, hcos, hhalf, hjor]
  exact frobNorm_le_of_frobSq_le (by positivity) hkey

/-! ## §4 — `exp` in closed form, and `log ∘ exp = id` on `ν < π` -/

/-- **THE CLOSED FORM, TOTAL.** Valid at `ν X = 0` as well: there `X = 0`, `su2Exp 0 = 1`, and the
right-hand side is `cos 0 · 1 + (sin 0 · 0⁻¹) · 0 = 1`. -/
theorem exp_form {X : M2} (hX : IsSu2 X) :
    ((su2Exp X : SU2) : M2)
      = (Real.cos (nu X)) • (1 : M2) + (Real.sin (nu X) * (nu X)⁻¹) • X := by
  rcases eq_or_lt_of_le (nu_nonneg X) with h0 | h0
  · have hX0 : X = 0 := (nu_eq_zero_iff X).mp h0.symm
    subst hX0
    have hnu0 : nu (0 : M2) = 0 := (nu_eq_zero_iff 0).mpr rfl
    rw [hnu0]
    simp [su2Exp_zero]
  · have hcoe : ((su2Exp X : SU2) : M2) = NormedSpace.exp X :=
      su2Exp_of_mem (AdalyFormal.Balaban.ClassPropagationUbar.exp_mem_special hX.1 hX.2)
    rw [hcoe]
    exact AdalyFormal.Balaban.ClassPropagationUbar.exp_closed hX.1 hX.2 h0 (nu_sq X)

/-- `tr(exp X) = 2 cos(ν X)`, hence `θ(exp X) = ν X` whenever `ν X ≤ π`. -/
theorem angle_exp {X : M2} (hX : IsSu2 X) (h : nu X ≤ Real.pi) :
    su2Angle (su2Exp X) = nu X := by
  have htr : Matrix.trace ((su2Exp X : SU2) : M2) = ((2 * Real.cos (nu X) : ℝ) : ℂ) := by
    rw [exp_form hX, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
      hX.2]
    simp only [Fintype.card_fin, smul_zero, add_zero, Nat.cast_ofNat, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [su2Angle, htr]
  simp only [Complex.ofReal_re]
  rw [show 2 * Real.cos (nu X) / 2 = Real.cos (nu X) by ring]
  exact Real.arccos_cos (nu_nonneg X) h

theorem Yof_exp {X : M2} (hX : IsSu2 X) (h : nu X ≤ Real.pi) :
    Yof (su2Exp X) = (Real.sin (nu X) * (nu X)⁻¹) • X := by
  rw [Yof, angle_exp hX h, exp_form hX, real_smul_eq]
  abel

/-- **`log ∘ exp = id` on `𝔰𝔲(2)` inside the principal ball `ν X < π`.** -/
theorem log_exp {X : M2} (hX : IsSu2 X) (h : nu X < Real.pi) : su2Log (su2Exp X) = X := by
  rcases eq_or_lt_of_le (nu_nonneg X) with h0 | h0
  · have hX0 : X = 0 := (nu_eq_zero_iff X).mp h0.symm
    rw [hX0] at *
    simpa using congrArg su2Log (su2Exp_zero)
  · have hs : 0 < Real.sin (nu X) := Real.sin_pos_of_pos_of_lt_pi h0 h
    rw [su2Log_eq_kappa_smul, Yof_exp hX (le_of_lt h), su2Kappa, angle_exp hX (le_of_lt h),
      real_smul_eq, smul_smul]
    rw [show nu X / Real.sin (nu X) * (Real.sin (nu X) * (nu X)⁻¹) = 1 by
      field_simp]
    exact one_smul _ X

/-- The real-scalar form of `sq_eq`, and the real-scalar `(a•1+C)(a•1−C)` expansion. -/
theorem sq_eq_real {X : M2} (hX : IsSu2 X) : X * X = (-(nu X ^ 2)) • (1 : M2) := by
  rw [sq_eq hX, real_smul_eq]

theorem central_expand_real (a : ℝ) (C : M2) :
    (a • (1 : M2) + C) * (a • (1 : M2) - C) = (a * a) • (1 : M2) - C * C := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  module

theorem cos_sq_add_sinc_sq (r : ℝ) :
    Real.cos r * Real.cos r
      - Real.sin r * r⁻¹ * (Real.sin r * r⁻¹) * (-(r ^ 2)) = 1 := by
  rcases eq_or_ne r 0 with h | h
  · rw [h]; simp
  · field_simp
    nlinarith [Real.sin_sq_add_cos_sq r]

/-- `exp A · exp (−A) = 1` — needed only for the degenerate corner `A + B = 0` of §5. -/
theorem exp_mul_exp_neg {A : M2} (hA : IsSu2 A) :
    ((su2Exp A : SU2) : M2) * ((su2Exp (-A) : SU2) : M2) = 1 := by
  have hA' : IsSu2 (-A) := hA.neg
  have hnn : nu (-A) = nu A := nu_neg A
  rw [exp_form hA, exp_form hA', hnn]
  have e2 : (Real.cos (nu A)) • (1 : M2) + (Real.sin (nu A) * (nu A)⁻¹) • (-A)
      = (Real.cos (nu A)) • (1 : M2) - (Real.sin (nu A) * (nu A)⁻¹) • A := by module
  rw [e2, central_expand_real, Matrix.smul_mul, Matrix.mul_smul, sq_eq_real hA,
    smul_smul, smul_smul, ← sub_smul, cos_sq_add_sinc_sq, one_smul]

/-! ## §5 — LEMMA G: `‖exp A · exp B − exp(A+B)‖_F ≤ 4‖A‖_F‖B‖_F` on `ν A + ν B ≤ π/2` -/

/-- `sinc x = sin x / x`, with Lean's `sinc 0 = 0`. -/
noncomputable def sinc (x : ℝ) : ℝ := Real.sin x / x

theorem sinc_eq (x : ℝ) : sinc x = Real.sin x * x⁻¹ := div_eq_mul_inv _ _

theorem sinc_nonneg {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ Real.pi) : 0 ≤ sinc x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [sinc, ← h]; simp
  · exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx hx2) hx

theorem sinc_le_one {x : ℝ} (hx : 0 ≤ x) : sinc x ≤ 1 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [sinc, ← h]; simp
  · rw [sinc, div_le_one h]; exact Real.sin_le hx

/-- `sinc` is 1-Lipschitz on `(0, 2]`. The derivative bound is
`|t cos t − sin t|/t² = (sin t − t cos t)/t² ≤ (t³/2)/t² = t/2 ≤ 1`; the SIGN comes from
`Real.lt_tan` below `π/2` and from `cos ≤ 0 ≤ sin` above it, and the SIZE from `sin t ≤ t`
together with `cos t ≥ 1 − t²/2`. -/
theorem sinc_lipschitz {x y : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) (hy : 0 < y) (hy2 : y ≤ 2) :
    |sinc x - sinc y| ≤ |x - y| := by
  have hpi := Real.pi_gt_three
  set m : ℝ := min x y with hm
  have hm0 : 0 < m := lt_min hx hy
  set S : Set ℝ := Set.Icc m 2 with hS
  have hxS : x ∈ S := ⟨min_le_left _ _, hx2⟩
  have hyS : y ∈ S := ⟨min_le_right _ _, hy2⟩
  have hconv : Convex ℝ S := convex_Icc _ _
  have hderiv : ∀ t ∈ S, HasDerivWithinAt sinc
      ((Real.cos t * t - Real.sin t * 1) / t ^ 2) S t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hm0 ht.1)
    exact ((Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht0).hasDerivWithinAt
  have hbound : ∀ t ∈ S, ‖(Real.cos t * t - Real.sin t * 1) / t ^ 2‖ ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hm0 ht.1
    have ht2 : t ≤ 2 := ht.2
    have hsign : 0 ≤ Real.sin t - t * Real.cos t := by
      rcases le_or_gt t (Real.pi / 2) with hc | hc
      · rcases eq_or_lt_of_le hc with he | he
        · rw [he]; simp
        · have hlt := Real.lt_tan ht0 he
          have hcp : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, he⟩
          rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcp] at hlt
          nlinarith
      · have hcn : Real.cos t ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_lt hc) (by linarith)
        have hsn : 0 ≤ Real.sin t :=
          le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith))
        nlinarith
    have hsize : Real.sin t - t * Real.cos t ≤ t ^ 3 / 2 := by
      have h1 : Real.sin t ≤ t := Real.sin_le (le_of_lt ht0)
      have h2 : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
      nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2),
      div_le_one (by positivity), abs_le]
    constructor <;> nlinarith
  have hres := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hxS hyS
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hres
  rw [abs_sub_comm (sinc x), abs_sub_comm x y]
  exact hres

/-- `|α − γ| ≤ β` where `γ = ν(A+B)` — pure Cauchy–Schwarz. -/
theorem abs_nu_add_sub_le {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B) :
    |nu (A + B) - nu A| ≤ nu B := by
  have hsq : nu (A + B) ^ 2 = nu A ^ 2 + ip A B + nu B ^ 2 := by
    rw [nu_sq, nu_sq, nu_sq, frobSq_add]; ring
  have hcs := abs_ip_le hA hB
  rw [abs_le] at hcs
  have hup : nu (A + B) ≤ nu A + nu B := by
    refine le_trans (le_abs_self _) (abs_le_of_sq_le_sq' ?_
      (by linarith [nu_nonneg A, nu_nonneg B]))
    · nlinarith [hcs.2]
  have hlo : nu A - nu B ≤ nu (A + B) := by
    have h := abs_le_of_sq_le_sq' (a := nu A - nu B) (b := nu (A + B)) (by nlinarith [hcs.1])
      (nu_nonneg _)
    exact le_trans (le_abs_self _) h
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- `|cos α cos β − cos γ| ≤ 2 sin α sin β` — BOTH numbers lie in `[cos(α+β), cos(α−β)]`, an
interval of length exactly `2 sin α sin β`. -/
theorem cos_prod_sub_cos_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ Real.pi)
    (hc0 : |a - b| ≤ c) (hc1 : c ≤ a + b) :
    |Real.cos a * Real.cos b - Real.cos c| ≤ 2 * (Real.sin a * Real.sin b) := by
  have hpi := Real.pi_pos
  obtain ⟨hl, hu⟩ := abs_le.mp hc0
  have hcnn : 0 ≤ c := le_trans (abs_nonneg _) hc0
  have h1 : Real.cos (a + b) ≤ Real.cos c :=
    Real.cos_le_cos_of_nonneg_of_le_pi hcnn hab hc1
  have h2 : Real.cos c ≤ Real.cos (a - b) := by
    rcases le_total a b with hab' | hab'
    · have hsym : Real.cos (a - b) = Real.cos (b - a) := by
        rw [← Real.cos_neg (b - a)]; congr 1; ring
      rw [hsym]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    · exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hsum : Real.cos (a - b) + Real.cos (a + b) = 2 * (Real.cos a * Real.cos b) := by
    rw [Real.cos_sub, Real.cos_add]; ring
  have hdiff : Real.cos (a - b) - Real.cos (a + b) = 2 * (Real.sin a * Real.sin b) := by
    rw [Real.cos_sub, Real.cos_add]; ring
  rw [abs_le]
  constructor <;> linarith

/-! ### §5a — the product of two exponentials, in closed form -/

/-- The `𝔰𝔲(2)` part of `exp A · exp B`. -/
noncomputable def prodVec (A B : M2) : M2 :=
  (Real.cos (nu B) * sinc (nu A)) • A + ((Real.cos (nu A) * sinc (nu B)) • B
    + (sinc (nu A) * sinc (nu B)) • comm2 A B)

/-- The scalar part of `exp A · exp B`. -/
noncomputable def prodSc (A B : M2) : ℝ :=
  Real.cos (nu A) * Real.cos (nu B) - sinc (nu A) * sinc (nu B) * (ip A B / 2)

theorem isSu2_prodVec {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B) : IsSu2 (prodVec A B) :=
  (hA.smul _).add ((hB.smul _).add ((hA.comm2 hB).smul _))

/-- **THE PRODUCT FORMULA.** Unconditional: `exp_form` is total, so no positivity of `ν` is
needed. -/
theorem exp_mul_exp_form {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B) :
    ((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
      = (prodSc A B) • (1 : M2) + prodVec A B := by
  rw [exp_form hA, exp_form hB, ← sinc_eq, ← sinc_eq]
  have hAB : A * B = (-(ip A B) / 2) • (1 : M2) + comm2 A B := by
    rw [mul_eq hA hB, real_smul_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul]
  rw [hAB, prodSc, prodVec]
  module

theorem trace_prod {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B) :
    (Matrix.trace (((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2))).re / 2 = prodSc A B := by
  rw [exp_mul_exp_form hA hB, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    (isSu2_prodVec hA hB).2]
  simp only [Fintype.card_fin, add_zero, Nat.cast_ofNat, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num

/-! ### §5b — the degenerate corners and the bound -/

theorem frobNorm_le_of_frobSq_le_sq {c : ℝ} (hc : 0 ≤ c) {X : M2} (h : frobSq X ≤ c ^ 2) :
    frobNorm X ≤ c := by
  unfold frobNorm
  calc Real.sqrt (frobSq X) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

theorem one_sub_cos_le {x : ℝ} : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  have h1 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h2 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  rw [abs_le]; constructor <;> linarith

/-- **LEMMA G.** `‖exp A · exp B − exp(A+B)‖_F ≤ 8·ν A·ν B` on `ν A + ν B ≤ π/2`.

Equivalently `≤ 4·‖A‖_F·‖B‖_F` (`group_bilinear_frobNorm`). The reference point `exp(A+B)` is
what makes a term-by-term bound possible at all: against `A + B` the corresponding split cancels
to higher order and the triangle inequality destroys the estimate. -/
theorem group_bilinear {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B)
    (hdom : nu A + nu B ≤ Real.pi / 2) :
    frobNorm (((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
      - ((su2Exp (A + B) : SU2) : M2)) ≤ 8 * (nu A * nu B) := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have hS : IsSu2 (A + B) := hA.add hB
  have hna := nu_nonneg A
  have hnb := nu_nonneg B
  have hng := nu_nonneg (A + B)
  -- degenerate corners
  rcases eq_or_lt_of_le hna with hA0 | hA0
  · have : A = 0 := (nu_eq_zero_iff A).mp hA0.symm
    subst this
    rw [su2Exp_zero]
    simp only [coe_one, Matrix.one_mul, zero_add, sub_self]
    rw [show frobNorm (0 : M2) = 0 by simp [frobNorm, frobSq]]
    rw [← hA0]; simp
  rcases eq_or_lt_of_le hnb with hB0 | hB0
  · have : B = 0 := (nu_eq_zero_iff B).mp hB0.symm
    subst this
    rw [su2Exp_zero]
    simp only [coe_one, Matrix.mul_one, add_zero, sub_self]
    rw [show frobNorm (0 : M2) = 0 by simp [frobNorm, frobSq]]
    rw [← hB0]; simp
  rcases eq_or_lt_of_le hng with hG0 | hG0
  · have hz : A + B = 0 := (nu_eq_zero_iff _).mp hG0.symm
    have hBA : B = -A := by
      have : B = (A + B) - A := by abel
      rw [this, hz]; abel
    have hzero : ((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
        - ((su2Exp (A + B) : SU2) : M2) = 0 := by
      rw [hBA, show A + -A = (0 : M2) by abel, su2Exp_zero, coe_one, exp_mul_exp_neg hA,
        sub_self]
    rw [hzero, show frobNorm (0 : M2) = 0 by simp [frobNorm, frobSq]]
    exact mul_nonneg (by norm_num) (mul_nonneg (nu_nonneg A) (nu_nonneg B))
  -- main case
  set al := nu A with hal
  set be := nu B with hbe
  set ga := nu (A + B) with hga
  set a := sinc al with hsa
  set b := sinc be with hsb
  set c := sinc ga with hsc
  have hal2 : al ≤ Real.pi / 2 := by linarith
  have hbe2 : be ≤ Real.pi / 2 := by linarith
  have hga_lo : |ga - al| ≤ be := abs_nu_add_sub_le hA hB
  have hga_lo' : |ga - be| ≤ al := by
    have h := abs_nu_add_sub_le hB hA
    rw [show B + A = A + B by abel] at h
    exact h
  have hga2 : ga ≤ Real.pi / 2 := by
    have := (abs_le.mp hga_lo).2; linarith
  have ha01 : 0 ≤ a ∧ a ≤ 1 := ⟨sinc_nonneg hna (by linarith), sinc_le_one hna⟩
  have hb01 : 0 ≤ b ∧ b ≤ 1 := ⟨sinc_nonneg hnb (by linarith), sinc_le_one hnb⟩
  have hc01 : 0 ≤ c ∧ c ≤ 1 := ⟨sinc_nonneg hng (by linarith), sinc_le_one hng⟩
  -- the difference, in the `c•1 + W` form
  set Wv : M2 := (Real.cos be * a - c) • A
      + ((Real.cos al * b - c) • B + (a * b) • comm2 A B) with hWv
  have hD : ((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
        - ((su2Exp (A + B) : SU2) : M2)
      = (prodSc A B - Real.cos ga) • (1 : M2) + (1 : ℝ) • Wv := by
    rw [hWv, exp_mul_exp_form hA hB, exp_form hS, ← sinc_eq, ← hga, ← hsc, prodVec, ← hal, ← hbe,
      ← hsa, ← hsb]
    have hsplit : c • (A + B) = c • A + c • B := by module
    rw [hsplit, sub_smul, one_smul]
    module
  have hW : IsSu2 Wv := by
    rw [hWv]; exact (hA.smul _).add ((hB.smul _).add ((hA.comm2 hB).smul _))
  -- scalar part
  have hI : |ip A B| ≤ 2 * (al * be) := abs_ip_le hA hB
  have hsinal : Real.sin al ≤ al := Real.sin_le hna
  have hsinbe : Real.sin be ≤ be := Real.sin_le hnb
  have hsinal0 : 0 ≤ Real.sin al := Real.sin_nonneg_of_nonneg_of_le_pi hna (by linarith)
  have hsinbe0 : 0 ≤ Real.sin be := Real.sin_nonneg_of_nonneg_of_le_pi hnb (by linarith)
  have hcc : |Real.cos al * Real.cos be - Real.cos ga| ≤ 2 * (Real.sin al * Real.sin be) := by
    refine cos_prod_sub_cos_le hna hnb (by linarith) ?_ ?_
    · rw [abs_le]
      constructor <;> [linarith [(abs_le.mp hga_lo').1]; linarith [(abs_le.mp hga_lo).1]]
    · linarith [(abs_le.mp hga_lo).2]
  have hDc : |prodSc A B - Real.cos ga| ≤ 3 * (al * be) := by
    rw [prodSc, ← hal, ← hbe, ← hsa, ← hsb]
    have hX : |ip A B| / 2 ≤ al * be := by linarith
    have hXnn : (0:ℝ) ≤ |ip A B| / 2 := by positivity
    have hterm : |a * b * (ip A B / 2)| ≤ al * be := by
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg ha01.1, abs_of_nonneg hb01.1, abs_two]
      calc a * b * (|ip A B| / 2) ≤ 1 * 1 * (|ip A B| / 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hXnn
            nlinarith [ha01.1, ha01.2, hb01.1, hb01.2]
        _ = |ip A B| / 2 := by ring
        _ ≤ al * be := hX
    have hrw : Real.cos al * Real.cos be - a * b * (ip A B / 2) - Real.cos ga
        = (Real.cos al * Real.cos be - Real.cos ga) - a * b * (ip A B / 2) := by ring
    rw [hrw]
    calc |Real.cos al * Real.cos be - Real.cos ga - a * b * (ip A B / 2)|
        ≤ |Real.cos al * Real.cos be - Real.cos ga| + |a * b * (ip A B / 2)| := abs_sub _ _
      _ ≤ 2 * (Real.sin al * Real.sin be) + al * be := by linarith
      _ ≤ 3 * (al * be) := by nlinarith
  -- vector part
  have hac : |a - c| ≤ be := by
    have hlip := sinc_lipschitz hA0 (by linarith) hG0 (by linarith)
    rw [← hsa, ← hsc] at hlip
    calc |a - c| ≤ |al - ga| := hlip
      _ = |ga - al| := abs_sub_comm _ _
      _ ≤ be := hga_lo
  have hbc : |b - c| ≤ al := by
    have hlip := sinc_lipschitz hB0 (by linarith) hG0 (by linarith)
    rw [← hsb, ← hsc] at hlip
    calc |b - c| ≤ |be - ga| := hlip
      _ = |ga - be| := abs_sub_comm _ _
      _ ≤ al := hga_lo'
  have hco1 : |Real.cos be * a - c| ≤ be ^ 2 / 2 + be := by
    have h1 : |Real.cos be * a - a| ≤ be ^ 2 / 2 := by
      rw [show Real.cos be * a - a = (Real.cos be - 1) * a by ring, abs_mul,
        abs_of_nonneg ha01.1]
      nlinarith [one_sub_cos_le (x := be), abs_nonneg (Real.cos be - 1), ha01.1, ha01.2]
    calc |Real.cos be * a - c| ≤ |Real.cos be * a - a| + |a - c| := by
          have := abs_sub_le (Real.cos be * a) a c; linarith
      _ ≤ be ^ 2 / 2 + be := by linarith
  have hco2 : |Real.cos al * b - c| ≤ al ^ 2 / 2 + al := by
    have h1 : |Real.cos al * b - b| ≤ al ^ 2 / 2 := by
      rw [show Real.cos al * b - b = (Real.cos al - 1) * b by ring, abs_mul,
        abs_of_nonneg hb01.1]
      nlinarith [one_sub_cos_le (x := al), abs_nonneg (Real.cos al - 1), hb01.1, hb01.2]
    calc |Real.cos al * b - c| ≤ |Real.cos al * b - b| + |b - c| := by
          have := abs_sub_le (Real.cos al * b) b c; linarith
      _ ≤ al ^ 2 / 2 + al := by linarith
  have hK : nu (comm2 A B) ≤ al * be := nu_comm2_le hA hB
  have hDw : nu Wv ≤ 4 * (al * be) := by
    have h1 : nu Wv ≤ |Real.cos be * a - c| * nu A
        + nu ((Real.cos al * b - c) • B + (a * b) • comm2 A B) := by
      rw [hWv]
      have := nu_add_le ((Real.cos be * a - c) • A)
        ((Real.cos al * b - c) • B + (a * b) • comm2 A B)
      rwa [nu_smul] at this
    have h2 : nu ((Real.cos al * b - c) • B + (a * b) • comm2 A B)
        ≤ |Real.cos al * b - c| * nu B + |a * b| * nu (comm2 A B) := by
      have := nu_add_le ((Real.cos al * b - c) • B) ((a * b) • comm2 A B)
      rwa [nu_smul, nu_smul] at this
    rw [← hal] at h1
    rw [← hbe] at h2
    have hab : |a * b| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha01.1, abs_of_nonneg hb01.1]
      nlinarith [ha01.1, ha01.2, hb01.1, hb01.2]
    have e1 : |Real.cos be * a - c| * al ≤ (be ^ 2 / 2 + be) * al := by nlinarith [hco1, hna]
    have e2 : |Real.cos al * b - c| * be ≤ (al ^ 2 / 2 + al) * be := by nlinarith [hco2, hnb]
    have e3 : |a * b| * nu (comm2 A B) ≤ al * be := by
      nlinarith [hK, nu_nonneg (comm2 A B), hab, abs_nonneg (a * b)]
    have hsum2 : al + be ≤ 2 := by linarith
    have hbound : (be ^ 2 / 2 + be) * al + ((al ^ 2 / 2 + al) * be + al * be)
        ≤ 4 * (al * be) := by nlinarith [mul_nonneg hna hnb, hsum2, hna, hnb]
    linarith
  -- assemble
  have hfrob : frobSq (((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
      - ((su2Exp (A + B) : SU2) : M2)) ≤ (8 * (al * be)) ^ 2 := by
    rw [hD, AdalyFormal.Balaban.ClassPropagationUbar.comb_frobSq hW.1 hW.2]
    have hq : frobSq Wv = 2 * (nu Wv) ^ 2 := by have := nu_sq Wv; linarith
    rw [hq]
    have hDc' : (prodSc A B - Real.cos ga) ^ 2 ≤ (3 * (al * be)) ^ 2 := by
      have h := abs_le.mp hDc; nlinarith [h.1, h.2]
    have hDw' : (nu Wv) ^ 2 ≤ (4 * (al * be)) ^ 2 := by
      nlinarith [hDw, nu_nonneg Wv]
    nlinarith [hDc', hDw', mul_nonneg hna hnb]
  exact frobNorm_le_of_frobSq_le_sq (by positivity) hfrob

/-! ## §6 — THE BCH-2 THEOREM -/

theorem sinc_mul (x : ℝ) : sinc x * x = Real.sin x := by
  rcases eq_or_ne x 0 with h | h
  · rw [h]; simp
  · rw [sinc]; field_simp

theorem frobNorm_smul (r : ℝ) (X : M2) : frobNorm (r • X) = |r| * frobNorm X := by
  unfold frobNorm
  rw [frobSq_smul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

theorem frobNorm_nonneg (X : M2) : 0 ≤ frobNorm X := Real.sqrt_nonneg _

/-- The angle of `exp A · exp B` stays inside the cap, because
`cos θ(gh) ≥ cos α cos β − sin α sin β = cos(α+β) ≥ 0`. -/
theorem angle_prod_le {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B)
    (hdom : nu A + nu B ≤ Real.pi / 2) :
    su2Angle (su2Exp A * su2Exp B) ≤ Real.pi / 2 := by
  have hna := nu_nonneg A
  have hnb := nu_nonneg B
  have hpi := Real.pi_gt_three
  have hsc : (Matrix.trace (((su2Exp A * su2Exp B : SU2)) : M2)).re / 2 = prodSc A B := by
    rw [coe_mul]; exact trace_prod hA hB
  rw [su2Angle, hsc, Real.arccos_le_pi_div_two]
  have ha0 : 0 ≤ sinc (nu A) := sinc_nonneg hna (by linarith)
  have hb0 : 0 ≤ sinc (nu B) := sinc_nonneg hnb (by linarith)
  have hI : |ip A B| ≤ 2 * (nu A * nu B) := abs_ip_le hA hB
  have hterm : sinc (nu A) * sinc (nu B) * (ip A B / 2)
      ≤ Real.sin (nu A) * Real.sin (nu B) := by
    have h1 : ip A B / 2 ≤ nu A * nu B := by
      linarith [(abs_le.mp hI).2]
    have h2 : sinc (nu A) * sinc (nu B) * (ip A B / 2)
        ≤ sinc (nu A) * sinc (nu B) * (nu A * nu B) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg ha0 hb0)
    have h3 : sinc (nu A) * sinc (nu B) * (nu A * nu B)
        = (sinc (nu A) * nu A) * (sinc (nu B) * nu B) := by ring
    rw [h3, sinc_mul, sinc_mul] at h2
    exact h2
  have hcosadd : Real.cos (nu A + nu B)
      = Real.cos (nu A) * Real.cos (nu B) - Real.sin (nu A) * Real.sin (nu B) := Real.cos_add _ _
  have hcnn : 0 ≤ Real.cos (nu A + nu B) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hdom⟩
  rw [prodSc]
  linarith

/-- **BCH-2 AT `su(2)`.**  For `A, B ∈ 𝔰𝔲(2)` with `ν A + ν B ≤ π/2`,

`‖log(exp A · exp B) − (A + B)‖_F ≤ 4π · ν A · ν B`.

Composed as `(π/2)` [LEMMA L, the log-Lipschitz constant on the cap] `× 8` [LEMMA G, the
group-level bilinear bound]. Both factors are separately kernel-checked; neither is fitted. -/
theorem bch2_nu {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B) (hdom : nu A + nu B ≤ Real.pi / 2) :
    frobNorm (su2Log (su2Exp A * su2Exp B) - (A + B)) ≤ (4 * Real.pi) * (nu A * nu B) := by
  have hpi := Real.pi_gt_three
  have hS : IsSu2 (A + B) := hA.add hB
  have hgam : nu (A + B) ≤ Real.pi / 2 := by
    have h := (abs_le.mp (abs_nu_add_sub_le hA hB)).2
    linarith [nu_nonneg A]
  have hlog : su2Log (su2Exp (A + B)) = A + B := log_exp hS (by linarith)
  have hang2 : su2Angle (su2Exp (A + B)) = nu (A + B) := angle_exp hS (by linarith)
  have hL := su2Log_lipschitz (angle_prod_le hA hB hdom) (g' := su2Exp (A + B))
    (by rw [hang2]; exact hgam)
  rw [hlog, coe_mul] at hL
  have hG := group_bilinear hA hB hdom
  have hmono : (Real.pi / 2) * frobNorm (((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
      - ((su2Exp (A + B) : SU2) : M2)) ≤ (Real.pi / 2) * (8 * (nu A * nu B)) :=
    mul_le_mul_of_nonneg_left hG (by linarith)
  calc frobNorm (su2Log (su2Exp A * su2Exp B) - (A + B))
      ≤ (Real.pi / 2) * frobNorm (((su2Exp A : SU2) : M2) * ((su2Exp B : SU2) : M2)
          - ((su2Exp (A + B) : SU2) : M2)) := hL
    _ ≤ (Real.pi / 2) * (8 * (nu A * nu B)) := hmono
    _ = (4 * Real.pi) * (nu A * nu B) := by ring

/-- `√2 ≤ π/2`, so the `‖·‖_F`-stated domain `‖A‖_F + ‖B‖_F ≤ 2` sits inside `ν A + ν B ≤ π/2`. -/
theorem sqrt_two_le_pi_div_two : Real.sqrt 2 ≤ Real.pi / 2 := by
  have h1 : Real.sqrt 2 ≤ 1.5 := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 := Real.pi_gt_d2
  linarith

theorem nu_mul_nu_eq {A B : M2} : nu A * nu B = frobNorm A * frobNorm B / 2 := by
  rw [frobNorm_eq_sqrt_two_mul_nu, frobNorm_eq_sqrt_two_mul_nu]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (-(nu A * nu B) / 2) * h

/-- **BCH-2, in the campaign's own units.** `‖A‖_F + ‖B‖_F ≤ 2` is a strictly SMALLER domain
than `ν A + ν B ≤ π/2` (`sqrt_two_le_pi_div_two`), and it contains the small-field class:
`frobSupBond < √2/2` forces `‖log g‖_F < 0.72` per bond. -/
theorem bch2_frobNorm {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B)
    (hdom : frobNorm A + frobNorm B ≤ 2) :
    frobNorm (su2Log (su2Exp A * su2Exp B) - (A + B))
      ≤ (2 * Real.pi) * (frobNorm A * frobNorm B) := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hnu : nu A + nu B ≤ Real.pi / 2 := by
    have hA' := frobNorm_eq_sqrt_two_mul_nu A
    have hB' := frobNorm_eq_sqrt_two_mul_nu B
    have hsum : Real.sqrt 2 * (nu A + nu B) ≤ 2 := by
      rw [mul_add, ← hA', ← hB']; exact hdom
    have hle : nu A + nu B ≤ Real.sqrt 2 := by nlinarith [hsum, h2, hss]
    linarith [sqrt_two_le_pi_div_two]
  have h := bch2_nu hA hB hnu
  rw [nu_mul_nu_eq] at h
  calc frobNorm (su2Log (su2Exp A * su2Exp B) - (A + B))
      ≤ 4 * Real.pi * (frobNorm A * frobNorm B / 2) := h
    _ = (2 * Real.pi) * (frobNorm A * frobNorm B) := by ring

/-- The same with a RATIONAL constant, for consumers that do not want `π` in an arithmetic
chain: `2π < 7`.

**Where the slack really sits (measured 2026-08-03, `logs/slack_probe_*.log`).** `7` is a rounding
gate, and it is a COARSE one: the exact content is T2's `2π = 6.2832…`, but this proof reaches the
rational constant through `Real.pi_lt_d2` (`π < 3.15`), so its own arithmetic bottoms out at
`2 × 3.15 = 6.3` — not at `2π`. Probed both sides: with the constant `629/100` this `nlinarith`
FAILS (and `6.29 > 2π`, so that mutated statement is TRUE — a pure proof-tightness failure, battery
entry `M22`); with `63/10` it SUCCEEDS. So `7` carries `≈ 0.7` of slack beyond what the proof
needs, and `0.0168` of that is the `π < 3.15` rounding. Nothing here is rounded in T2 itself, whose
constant is the exact symbolic `2 * Real.pi`. -/
theorem bch2_seven {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B)
    (hdom : frobNorm A + frobNorm B ≤ 2) :
    frobNorm (su2Log (su2Exp A * su2Exp B) - (A + B)) ≤ 7 * (frobNorm A * frobNorm B) := by
  have h := bch2_frobNorm hA hB hdom
  have hpi := Real.pi_lt_d2
  nlinarith [h, mul_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)]

/-! ## §7 — WITNESSES

Two controls here, both pinned (no `∃` over free data, S91); a third, **W3 — SHARPNESS**, is in
§9 and is pinned the same way. §9 is at the end of the file only because it needs `wJ`, defined
just below.

* **W1, NON-VACUITY.** A noncommuting pair strictly inside the domain at which the quantity
  bounded by `bch2_*` is STRICTLY POSITIVE. Without this the theorem could be an inequality
  between two zeros.
* **W2, the DOMAIN IS LOAD-BEARING (S82).** A pair OUTSIDE the domain at which `bch2_seven`'s
  conclusion is FALSE. So the hypothesis `‖A‖_F + ‖B‖_F ≤ 2` cannot be deleted, and the
  constant `7` cannot be made domain-free. -/

/-- `diag(i, −i)`. -/
noncomputable def wJ : M2 := Matrix.of ![![Complex.I, 0], ![0, -Complex.I]]

/-- The real antisymmetric generator `[[0,1],[−1,0]]`. -/
noncomputable def wK : M2 := Matrix.of ![![0, 1], ![-1, 0]]

theorem isSu2_wJ : IsSu2 wJ := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [wJ, Matrix.conjTranspose_apply, Matrix.of_apply]
  · simp [wJ, Matrix.trace_fin_two, Matrix.of_apply]

theorem isSu2_wK : IsSu2 wK := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [wK, Matrix.conjTranspose_apply, Matrix.of_apply]
  · simp [wK, Matrix.trace_fin_two, Matrix.of_apply]

theorem frobSq_wJ : frobSq wJ = 2 := by
  simp [frobSq, wJ, Matrix.of_apply, Complex.normSq_apply]
  norm_num

theorem frobSq_wK : frobSq wK = 2 := by
  simp [frobSq, wK, Matrix.of_apply, Complex.normSq_apply]
  norm_num

theorem nu_wJ : nu wJ = 1 := by
  rw [nu, frobSq_wJ]; norm_num

theorem nu_wK : nu wK = 1 := by
  rw [nu, frobSq_wK]; norm_num

theorem frobNorm_wJ : frobNorm wJ = Real.sqrt 2 := by rw [frobNorm, frobSq_wJ]

theorem nu_smul_wJ {r : ℝ} (hr : 0 ≤ r) : nu (r • wJ) = r := by
  rw [nu_smul, nu_wJ, abs_of_nonneg hr, mul_one]

theorem nu_smul_wK {r : ℝ} (hr : 0 ≤ r) : nu (r • wK) = r := by
  rw [nu_smul, nu_wK, abs_of_nonneg hr, mul_one]

/-! ### W1 — a noncommuting pair inside the domain, with a strictly positive defect -/

noncomputable def wA : M2 := (1/2 : ℝ) • wJ
noncomputable def wB : M2 := (1/2 : ℝ) • wK

theorem isSu2_wA : IsSu2 wA := isSu2_wJ.smul _
theorem isSu2_wB : IsSu2 wB := isSu2_wK.smul _
theorem nu_wA : nu wA = 1/2 := nu_smul_wJ (by norm_num)
theorem nu_wB : nu wB = 1/2 := nu_smul_wK (by norm_num)

theorem wA_dom : frobNorm wA + frobNorm wB ≤ 2 := by
  rw [frobNorm_eq_sqrt_two_mul_nu, frobNorm_eq_sqrt_two_mul_nu, nu_wA, nu_wB]
  have h1 : Real.sqrt 2 ≤ 1.5 := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- The pair genuinely does NOT commute. -/
theorem wA_wB_noncomm : wA * wB ≠ wB * wA := by
  intro h
  have h2 := congrFun (congrFun h 0) 1
  simp [wA, wB, wJ, wK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Complex.ext_iff] at h2
  norm_num at h2

theorem comm2_wA_wB_apply : comm2 wA wB 0 1 = Complex.I / 4 := by
  simp [comm2, wA, wB, wJ, wK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.sub_apply, Matrix.smul_apply, Complex.ext_iff]
  ring

theorem sinc_half_pos : 0 < sinc (1/2 : ℝ) := by
  rw [sinc]
  have : 0 < Real.sin (1/2 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  positivity

/-- **W1a.** `exp wA · exp wB ≠ exp (wA + wB)` — LEMMA G's left-hand side is not identically
zero on the domain. The separation is read off the `(0,1)` entry: on the left it acquires the
imaginary part `sinc(½)²/4 > 0` from the commutator term, on the right the entry is real. -/
theorem prod_ne_exp_add :
    ((su2Exp wA : SU2) : M2) * ((su2Exp wB : SU2) : M2) ≠ ((su2Exp (wA + wB) : SU2) : M2) := by
  intro h
  have hL := exp_mul_exp_form isSu2_wA isSu2_wB
  have hR := exp_form (isSu2_wA.add isSu2_wB)
  rw [hL, hR] at h
  have h01 := congrFun (congrFun h 0) 1
  rw [prodVec] at h01
  have hwA01 : wA 0 1 = 0 := by simp [wA, wJ, Matrix.smul_apply, Matrix.of_apply]
  have hwB01 : wB 0 1 = (1/2 : ℂ) := by
    simp [wB, wK, Matrix.smul_apply, Matrix.of_apply]
  have him := congrArg Complex.im h01
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide : (0:Fin 2) ≠ 1),
    smul_zero, Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, hwA01, hwB01, comm2_wA_wB_apply] at him
  rw [nu_wA, nu_wB] at him
  norm_num [Complex.div_im] at him
  have hpos : 0 < sinc (1/2 : ℝ) := sinc_half_pos
  nlinarith [him, hpos]

/-- `su2Log` is injective on the cap, because `exp ∘ log = id` off the single antipode. -/
theorem su2Log_inj_of_angle {g g' : SU2} (hg : su2Angle g ≤ Real.pi / 2)
    (hg' : su2Angle g' ≤ Real.pi / 2) (h : su2Log g = su2Log g') : g = g' := by
  have hpi := Real.pi_gt_three
  have hne : ∀ x : SU2, su2Angle x ≤ Real.pi / 2 → x ≠ su2NegOne := by
    intro x hx hcon
    rw [hcon] at hx
    have : su2Angle su2NegOne = Real.pi := by
      have htr : Matrix.trace ((su2NegOne : SU2) : M2) = -2 := by
        simp [su2NegOne, Matrix.trace_fin_two]
      rw [su2Angle, htr]
      norm_num
    rw [this] at hx
    linarith
  have h1 := AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne g (hne g hg)
  have h2 := AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne g' (hne g' hg')
  rw [← h1, ← h2, h]

/-- **W1b — NON-VACUITY OF `bch2_*`.** At the pinned noncommuting pair `wA, wB` inside the
domain, the quantity bounded by `bch2_nu` / `bch2_frobNorm` / `bch2_seven` is STRICTLY
POSITIVE. -/
theorem bch2_nonvacuous :
    0 < frobNorm (su2Log (su2Exp wA * su2Exp wB) - (wA + wB)) := by
  have hpi := Real.pi_gt_three
  have hS := isSu2_wA.add isSu2_wB
  have hdom : nu wA + nu wB ≤ Real.pi / 2 := by rw [nu_wA, nu_wB]; linarith
  have hgam : nu (wA + wB) ≤ Real.pi / 2 := by
    have h := (abs_le.mp (abs_nu_add_sub_le isSu2_wA isSu2_wB)).2
    linarith [nu_nonneg wA]
  have hang1 : su2Angle (su2Exp wA * su2Exp wB) ≤ Real.pi / 2 :=
    angle_prod_le isSu2_wA isSu2_wB hdom
  have hang2 : su2Angle (su2Exp (wA + wB)) ≤ Real.pi / 2 := by
    rw [angle_exp hS (by linarith)]; exact hgam
  have hne : su2Log (su2Exp wA * su2Exp wB) ≠ wA + wB := by
    intro hcon
    have hlog : su2Log (su2Exp (wA + wB)) = wA + wB := log_exp hS (by linarith)
    have := su2Log_inj_of_angle hang1 hang2 (by rw [hlog]; exact hcon)
    exact prod_ne_exp_add (by rw [← coe_mul, this])
  have hnz : su2Log (su2Exp wA * su2Exp wB) - (wA + wB) ≠ 0 := sub_ne_zero.mpr hne
  rcases eq_or_lt_of_le (frobNorm_nonneg (su2Log (su2Exp wA * su2Exp wB) - (wA + wB))) with h | h
  · exfalso
    apply hnz
    have hfs : frobSq (su2Log (su2Exp wA * su2Exp wB) - (wA + wB)) = 0 := by
      have := congrArg (fun x => x ^ 2) h
      simp only [frobNorm] at this
      rw [Real.sq_sqrt (frobSq_nonneg _)] at this
      linarith [this]
    exact AdalyFormal.Balaban.AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero hfs
  · exact h

/-! ### W2 — the domain hypothesis is LOAD-BEARING (S82 control)

`bch2_seven` says `‖log(exp A exp B) − (A+B)‖_F ≤ 7‖A‖_F‖B‖_F` on `‖A‖_F + ‖B‖_F ≤ 2`. Delete
the domain hypothesis and the statement becomes FALSE. The witness is a COMMUTING pair on a
single axis, `A = 3·J`, `B = (21/100)·J`, whose combined angle `3.21` has crossed `π`: the
principal logarithm wraps, `log(exp A exp B) − (A+B) = −2π·J`, whose norm `2π√2 = 8.8858…`
exceeds `7‖A‖_F‖B‖_F = 7·1.26 = 8.82`.

Note what this control does and does not show. It shows the DOMAIN is load-bearing, not that any
particular intermediate lemma is; and the failure is a BRANCH failure of `su2Log`, not a failure
of the bilinear mechanism — the commutator term is exactly zero here. -/

noncomputable def vA : M2 := (3 : ℝ) • wJ
noncomputable def vB : M2 := (21/100 : ℝ) • wJ

theorem isSu2_vA : IsSu2 vA := isSu2_wJ.smul _
theorem isSu2_vB : IsSu2 vB := isSu2_wJ.smul _
theorem nu_vA : nu vA = 3 := by rw [vA]; exact nu_smul_wJ (by norm_num)
theorem nu_vB : nu vB = 21/100 := by rw [vB]; exact nu_smul_wJ (by norm_num)

theorem sqrt_two_gt : (1.414 : ℝ) < Real.sqrt 2 := by
  have h : (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  rw [h]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem frobNorm_vA : frobNorm vA = Real.sqrt 2 * 3 := by
  rw [frobNorm_eq_sqrt_two_mul_nu, nu_vA]

theorem frobNorm_vB : frobNorm vB = Real.sqrt 2 * (21/100) := by
  rw [frobNorm_eq_sqrt_two_mul_nu, nu_vB]

theorem comm2_smul_wJ (r s : ℝ) : comm2 (r • wJ) (s • wJ) = 0 := by
  rw [comm2, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, mul_comm s r, sub_self, smul_zero]

theorem ip_smul_wJ (r s : ℝ) : ip (r • wJ) (s • wJ) = 2 * (r * s) := by
  rw [ip_smul_left, ip_smul_right, ip_self, frobSq_wJ]; ring

/-- `exp(3J)·exp(0.21J) = cos(3.21)·1 + sin(3.21)·J`. -/
theorem vprod_form :
    ((su2Exp vA : SU2) : M2) * ((su2Exp vB : SU2) : M2)
      = (Real.cos (321/100 : ℝ)) • (1 : M2) + (Real.sin (321/100 : ℝ)) • wJ := by
  have hnA : nu vA = 3 := nu_vA
  have hnB : nu vB = 21/100 := nu_vB
  have hip : ip vA vB = 2 * (3 * (21/100 : ℝ)) := ip_smul_wJ 3 (21/100)
  have hc : comm2 vA vB = 0 := comm2_smul_wJ 3 (21/100)
  have h3 := sinc_mul (3 : ℝ)
  have h21 := sinc_mul (21/100 : ℝ)
  have hcos : Real.cos (321/100 : ℝ)
      = Real.cos 3 * Real.cos (21/100 : ℝ) - Real.sin 3 * Real.sin (21/100 : ℝ) := by
    have h := Real.cos_add 3 (21/100 : ℝ)
    rw [show (3 : ℝ) + 21/100 = 321/100 by norm_num] at h
    exact h
  have hsin : Real.sin (321/100 : ℝ)
      = Real.sin 3 * Real.cos (21/100 : ℝ) + Real.cos 3 * Real.sin (21/100 : ℝ) := by
    have h := Real.sin_add 3 (21/100 : ℝ)
    rw [show (3 : ℝ) + 21/100 = 321/100 by norm_num] at h
    exact h
  have hs3 : Real.sin 3 = sinc 3 * 3 := h3.symm
  have hs21 : Real.sin (21/100 : ℝ) = sinc (21/100 : ℝ) * (21/100 : ℝ) := h21.symm
  rw [exp_mul_exp_form isSu2_vA isSu2_vB, prodSc, prodVec, hnA, hnB, hip, hc, hcos, hsin,
    vA, vB, smul_zero, add_zero, smul_smul, smul_smul, ← add_smul, hs3, hs21]
  congr 1
  · ring
  · ring

theorem vtheta_bounds : 0 ≤ 2 * Real.pi - 321/100 ∧ 2 * Real.pi - 321/100 ≤ Real.pi := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  constructor <;> [linarith; linarith]

theorem vangle : su2Angle (su2Exp vA * su2Exp vB) = 2 * Real.pi - 321/100 := by
  have hb := vtheta_bounds
  have htr : (Matrix.trace (((su2Exp vA * su2Exp vB : SU2)) : M2)).re / 2
      = Real.cos (321/100 : ℝ) := by
    rw [coe_mul, vprod_form, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, isSu2_wJ.2]
    simp only [Fintype.card_fin, smul_zero, add_zero, Nat.cast_ofNat, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
  rw [su2Angle, htr, ← Real.cos_two_pi_sub (321/100 : ℝ), Real.arccos_cos hb.1 hb.2]

theorem vsin_neg : Real.sin (321/100 : ℝ) < 0 := by
  have hb := vtheta_bounds
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have hpos : 0 < Real.sin (2 * Real.pi - 321/100) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_two_pi_sub] at hpos
  linarith

/-- **W2a.** The principal logarithm of the product, computed exactly: `−(2π − 3.21)·J`. -/
theorem vlog : su2Log (su2Exp vA * su2Exp vB) = (-(2 * Real.pi - 321/100)) • wJ := by
  have hsn := vsin_neg
  have hYof : Yof (su2Exp vA * su2Exp vB) = (Real.sin (321/100 : ℝ)) • wJ := by
    rw [Yof, vangle, coe_mul, vprod_form, Real.cos_two_pi_sub, real_smul_eq]
    abel
  have hsinth : Real.sin (2 * Real.pi - 321/100) = -Real.sin (321/100 : ℝ) :=
    Real.sin_two_pi_sub _
  have hkap : su2Kappa (su2Exp vA * su2Exp vB)
      = (2 * Real.pi - 321/100) / (-Real.sin (321/100 : ℝ)) := by
    rw [su2Kappa, vangle, hsinth]
  have hne : Real.sin (321/100 : ℝ) ≠ 0 := ne_of_lt hsn
  rw [su2Log_eq_kappa_smul, hYof, hkap, real_smul_eq, smul_smul]
  congr 1
  field_simp

/-- **W2b — THE CONTROL FIRES.** Outside the domain, `bch2_seven`'s conclusion is FALSE. -/
theorem bch2_seven_fails_outside_domain :
    ¬ (frobNorm (su2Log (su2Exp vA * su2Exp vB) - (vA + vB))
        ≤ 7 * (frobNorm vA * frobNorm vB)) := by
  have hs2 : (1.414 : ℝ) < Real.sqrt 2 := sqrt_two_gt
  have hpi := Real.pi_gt_d2
  have hsum : vA + vB = (321/100 : ℝ) • wJ := by
    rw [vA, vB, ← add_smul]; congr 1; norm_num
  have hdiff : su2Log (su2Exp vA * su2Exp vB) - (vA + vB) = (-(2 * Real.pi)) • wJ := by
    rw [vlog, hsum, ← sub_smul]
    congr 1
    ring
  have hlhs : frobNorm (su2Log (su2Exp vA * su2Exp vB) - (vA + vB))
      = 2 * Real.pi * Real.sqrt 2 := by
    rw [hdiff, frobNorm_smul, frobNorm_wJ, abs_of_nonpos (by linarith)]
    ring
  have hnA : frobNorm vA = Real.sqrt 2 * 3 := frobNorm_vA
  have hnB : frobNorm vB = Real.sqrt 2 * (21/100) := frobNorm_vB
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hrhs : 7 * (frobNorm vA * frobNorm vB) = 882/100 := by
    rw [hnA, hnB]
    nlinarith [hss]
  rw [hlhs, hrhs]
  intro hcon
  nlinarith [hcon, hpi, hs2]

/-- And the witness really is OUTSIDE the domain — `‖A‖_F + ‖B‖_F = 3.21·√2 > 2`. -/
theorem v_outside_domain : ¬ (frobNorm vA + frobNorm vB ≤ 2) := by
  have hs2 : (1.414 : ℝ) < Real.sqrt 2 := sqrt_two_gt
  rw [frobNorm_vA, frobNorm_vB]
  intro hcon
  nlinarith [hcon, hs2]

/-! ## §8 — THE CONSUMER HANDOFF: the staircase transfers

The abelian staircase mechanism is `log(∏ᵢ exp Aᵢ) = Σᵢ Aᵢ` — an exact coboundary telescoping.
Nonabelian, that identity is FALSE, and what §8 shows is that BCH-2 is exactly the primitive that
repairs it: the telescoping holds up to a defect that is QUADRATIC in the total field strength,
uniformly in the number of steps.

`bch2_telescope`: for a finite ordered family in `𝔰𝔲(2)` with total Frobenius mass `S ≤ 1/8`,

    ‖log(∏ exp Aᵢ) − Σ Aᵢ‖_F  ≤  14 · S² .

The `14` is composed, not fitted: the recursion is `E' ≤ 7·a·(S + E) + E` from `bch2_seven`, and
~~`14 S²` is the smallest constant of the form `κ S²` that this recursion reproduces on the stated
domain~~ **— STRUCK 2026-08-03, and the strike is retained in place. That sentence was FALSE, and
it was contradicted by the rest of its own parenthesis two lines below it. Raised by the Sol gate,
`compute/sol_bch2/VERDICT.md` §A4 / `compute/sol_bch22/VERDICT.md` §A3 item 2. CORRECTION:**
`14 S²` is *a* constant of the form `κ S²` that this recursion reproduces; it is not the SMALLEST.
The recursion reproduces `κ S²` exactly when `7κ·S ≤ (2κ − 7)·S`, i.e. `κ ≥ 7/(2 − 7S)`, which at
`S = 1/8` is `κ ≥ 56/9 = 6.22…`. **The smallest such constant is therefore `56/9`, not `14`**, and
`14` is a round value above it carrying margin `14 − 56/9 = 70/9 = 7.78` in the constant and
`14(2 − 7/8) − 7 = 35/4` in the recursion's own coefficient — slack that is what makes `nlinarith`
close here. No sharpness is claimed for H1 anywhere: `SCOPE.md` §6 lists H1 among the constants that
are explicitly NOT sharp, and mutation `M9` (`14 → 6`) is a PROOF-TIGHTNESS test, not a falsity one.
`S ≤ 1/8` is what keeps every partial product inside `bch2_seven`'s own domain.

**TYPED DEBT — what is a hypothesis here and would have to be discharged by the consumer.**
`bch2_telescope` is UNCONDITIONAL given its hypotheses; the debt is in matching it to a stair
gauge. The three items are, explicitly:

1. **The stair must be a LIST of `𝔰𝔲(2)` logarithms.** Here the data is `L : List M2` with
   `∀ X ∈ L, IsSu2 X`. A stair-gauge consumer holds GROUP elements `U(b)`; converting them to
   `A b := su2Log (U b)` is `log_exp`/`su2_exp_log_of_ne_negOne` and needs each `U b` off the
   antipode. Not discharged here because no stair is in this file's scope.
2. **The smallness `S ≤ 1/8` is on the SUM over the stair**, not per bond. For a stair of length
   `ℓ` this reads `ℓ · sup_b ‖A b‖_F ≤ 1/8` — i.e. it costs a factor `ℓ`. Whether the consumer's
   own small-field class supplies that is the consumer's obligation, and is NOT asserted here.
3. **Curvature is not separated.** `bch2_telescope` bounds the TOTAL defect. The
   coboundary/curvature/BCH split of the stair-gauge cost would additionally require identifying
   which part of `Σ Aᵢ` is a coboundary — a statement about the stair's geometry, not about
   `𝔰𝔲(2)`, and nothing in this file asserts it. -/

theorem isSu2_su2Log (g : SU2) : IsSu2 (su2Log g) := by
  rw [su2Log_eq_kappa_smul, real_smul_eq]
  exact (isSu2_Yof g).smul _

theorem frobNorm_add_le (X Y : M2) : frobNorm (X + Y) ≤ frobNorm X + frobNorm Y := by
  have h := frobNorm_sub_le X (-Y)
  rwa [sub_neg_eq_add, frobNorm_neg] at h

theorem ne_negOne_of_angle_le {g : SU2} (h : su2Angle g ≤ Real.pi / 2) : g ≠ su2NegOne := by
  intro hcon
  rw [hcon] at h
  have hval : su2Angle su2NegOne = Real.pi := by
    have htr : Matrix.trace ((su2NegOne : SU2) : M2) = -2 := by
      simp [su2NegOne]
    rw [su2Angle, htr]
    norm_num
  rw [hval] at h
  linarith [Real.pi_gt_three]

theorem nu_dom_of_frobNorm {A B : M2} (h : frobNorm A + frobNorm B ≤ 2) :
    nu A + nu B ≤ Real.pi / 2 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsum : Real.sqrt 2 * (nu A + nu B) ≤ 2 := by
    rw [mul_add, ← frobNorm_eq_sqrt_two_mul_nu, ← frobNorm_eq_sqrt_two_mul_nu]; exact h
  have hle : nu A + nu B ≤ Real.sqrt 2 := by nlinarith [hsum, h2, hss]
  linarith [sqrt_two_le_pi_div_two]

/-- `∏ᵢ exp Aᵢ`, in the order of the list. -/
noncomputable def expProd : List M2 → SU2
  | [] => 1
  | X :: L => su2Exp X * expProd L

@[simp] theorem expProd_nil : expProd [] = 1 := rfl
@[simp] theorem expProd_cons (X : M2) (L : List M2) :
    expProd (X :: L) = su2Exp X * expProd L := rfl

theorem isSu2_listSum : ∀ (L : List M2), (∀ X ∈ L, IsSu2 X) → IsSu2 L.sum
  | [], _ => by simpa using IsSu2.zero
  | X :: L, h => by
      rw [List.sum_cons]
      exact (h X (by simp)).add (isSu2_listSum L (fun Y hY => h Y (by simp [hY])))

theorem frobNorm_listSum_le : ∀ (L : List M2),
    frobNorm L.sum ≤ (L.map frobNorm).sum
  | [] => by simp [frobNorm, frobSq]
  | X :: L => by
      rw [List.sum_cons, List.map_cons, List.sum_cons]
      exact le_trans (frobNorm_add_le X L.sum)
        (by linarith [frobNorm_listSum_le L])

theorem frobNorm_listMap_nonneg : ∀ (L : List M2), 0 ≤ (L.map frobNorm).sum
  | [] => by simp
  | X :: L => by
      rw [List.map_cons, List.sum_cons]
      linarith [frobNorm_nonneg X, frobNorm_listMap_nonneg L]

/-- **THE TELESCOPING CORE.** Carries the two structural invariants the induction needs
(`log ∘ ∏` lands in `𝔰𝔲(2)`, and `exp ∘ log` really recovers the partial product) alongside the
quantitative bound. -/
theorem bch2_telescope_core : ∀ (L : List M2), (∀ X ∈ L, IsSu2 X) →
    (L.map frobNorm).sum ≤ 1/8 →
    su2Exp (su2Log (expProd L)) = expProd L ∧
      frobNorm (su2Log (expProd L) - L.sum) ≤ 14 * ((L.map frobNorm).sum) ^ 2
  | [], _, _ => by
      refine ⟨?_, ?_⟩
      · rw [expProd_nil, su2Log_one, su2Exp_zero]
      · rw [expProd_nil, su2Log_one, List.sum_nil, sub_zero]
        simp [frobNorm, frobSq]
  | X :: L, hmem, hsmall => by
      have hX : IsSu2 X := hmem X (by simp)
      have hL : ∀ Y ∈ L, IsSu2 Y := fun Y hY => hmem Y (by simp [hY])
      have hSL0 : 0 ≤ (L.map frobNorm).sum := frobNorm_listMap_nonneg L
      have hX0 : 0 ≤ frobNorm X := frobNorm_nonneg X
      have hcons : ((X :: L).map frobNorm).sum = frobNorm X + (L.map frobNorm).sum := by
        rw [List.map_cons, List.sum_cons]
      rw [hcons] at hsmall
      have hSL : (L.map frobNorm).sum ≤ 1/8 := by linarith
      obtain ⟨hexp, hbnd⟩ := bch2_telescope_core L hL hSL
      set Y : M2 := su2Log (expProd L) with hY
      have hYs : IsSu2 Y := isSu2_su2Log _
      have hYnorm : frobNorm Y ≤ (L.map frobNorm).sum + 14 * ((L.map frobNorm).sum) ^ 2 := by
        have h1 : frobNorm Y ≤ frobNorm (Y - L.sum) + frobNorm L.sum := by
          have := frobNorm_add_le (Y - L.sum) L.sum
          rw [sub_add_cancel] at this
          exact this
        linarith [frobNorm_listSum_le L]
      have hdom2 : frobNorm X + frobNorm Y ≤ 2 := by nlinarith [hYnorm, hSL, hX0, hSL0]
      have hprod : expProd (X :: L) = su2Exp X * su2Exp Y := by
        rw [expProd_cons, hY, hexp]
      have hang : su2Angle (su2Exp X * su2Exp Y) ≤ Real.pi / 2 :=
        angle_prod_le hX hYs (nu_dom_of_frobNorm hdom2)
      refine ⟨?_, ?_⟩
      · rw [hprod]
        exact AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne _
          (ne_negOne_of_angle_le hang)
      · have hstep := bch2_seven hX hYs hdom2
        rw [← hprod] at hstep
        have htri : frobNorm (su2Log (expProd (X :: L)) - (X :: L).sum)
            ≤ frobNorm (su2Log (expProd (X :: L)) - (X + Y)) + frobNorm (Y - L.sum) := by
          have hrw : su2Log (expProd (X :: L)) - (X :: L).sum
              = (su2Log (expProd (X :: L)) - (X + Y)) + (Y - L.sum) := by
            rw [List.sum_cons]; abel
          rw [hrw]
          exact frobNorm_add_le _ _
        have hkey : frobNorm (su2Log (expProd (X :: L)) - (X :: L).sum)
            ≤ 7 * (frobNorm X * frobNorm Y) + 14 * ((L.map frobNorm).sum) ^ 2 := by
          linarith [htri, hstep, hbnd]
        rw [hcons]
        nlinarith [hkey, hYnorm, hX0, hSL0, hSL,
          mul_nonneg hX0 hSL0, sq_nonneg (frobNorm X)]

/-- **BCH-2, TELESCOPED — the form a stair-gauge consumer uses.** -/
theorem bch2_telescope (L : List M2) (hmem : ∀ X ∈ L, IsSu2 X)
    (hsmall : (L.map frobNorm).sum ≤ 1/8) :
    frobNorm (su2Log (expProd L) - L.sum) ≤ 14 * ((L.map frobNorm).sum) ^ 2 :=
  (bch2_telescope_core L hmem hsmall).2

/-- The `n = 2` instance of `bch2_telescope` is `bch2_seven` with a worse constant, which is the
consistency check that the induction is not proving something weaker than its own base step in
disguise. -/
theorem bch2_telescope_two {A B : M2} (hA : IsSu2 A) (hB : IsSu2 B)
    (hsmall : frobNorm A + frobNorm B ≤ 1/8) :
    frobNorm (su2Log (su2Exp A * su2Exp B) - (A + B))
      ≤ 14 * (frobNorm A + frobNorm B) ^ 2 := by
  have h := bch2_telescope [A, B] (by
    intro Z hZ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
    rcases hZ with h | h
    · rw [h]; exact hA
    · rw [h]; exact hB) (by simpa using hsmall)
  simpa [expProd, List.sum_cons] using h

/-! ### §8a — converting a GROUP small-field bound into an ALGEBRA one

The consumer measures `‖U − 1‖_F` (`frobSupBond`), while `bch2_frobNorm` wants `‖log U‖_F`.
`su2Log_lipschitz` at `g' = 1` converts, with the same `π/2`. -/

theorem su2Angle_one : su2Angle (1 : SU2) = 0 := by
  have htr : Matrix.trace ((1 : SU2) : M2) = 2 := by
    rw [coe_one, Matrix.trace_one]
    simp
  rw [su2Angle, htr]
  norm_num

/-- `‖log g‖_F ≤ (π/2)·‖g − 1‖_F` on the cap. So a per-bond group bound `‖U − 1‖_F ≤ 2/π`
delivers `‖log U‖_F ≤ 1`, and two such bonds satisfy `bch2_frobNorm`'s domain `≤ 2`. -/
theorem frobNorm_su2Log_le {g : SU2} (hg : su2Angle g ≤ Real.pi / 2) :
    frobNorm (su2Log g) ≤ (Real.pi / 2) * frobNorm ((g : M2) - 1) := by
  have h := su2Log_lipschitz hg (g' := (1 : SU2)) (by rw [su2Angle_one]; positivity)
  rwa [su2Log_one, sub_zero, coe_one] at h

/-- The exact per-bond threshold this file certifies: `‖U − 1‖_F ≤ 2/π` and `‖V − 1‖_F ≤ 2/π`
(both on the cap) put the pair inside `bch2_frobNorm`'s domain. -/
theorem dom_of_group_bound {g h : SU2} (hga : su2Angle g ≤ Real.pi / 2)
    (hha : su2Angle h ≤ Real.pi / 2) (hg : frobNorm ((g : M2) - 1) ≤ 2 / Real.pi)
    (hh : frobNorm ((h : M2) - 1) ≤ 2 / Real.pi) :
    frobNorm (su2Log g) + frobNorm (su2Log h) ≤ 2 := by
  have hpi := Real.pi_gt_three
  have h1 := frobNorm_su2Log_le hga
  have h2 := frobNorm_su2Log_le hha
  have e1 : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp
  have b1 : (Real.pi / 2) * frobNorm ((g : M2) - 1) ≤ 1 := by
    calc (Real.pi / 2) * frobNorm ((g : M2) - 1) ≤ (Real.pi / 2) * (2 / Real.pi) :=
          mul_le_mul_of_nonneg_left hg (by linarith)
      _ = 1 := e1
  have b2 : (Real.pi / 2) * frobNorm ((h : M2) - 1) ≤ 1 := by
    calc (Real.pi / 2) * frobNorm ((h : M2) - 1) ≤ (Real.pi / 2) * (2 / Real.pi) :=
          mul_le_mul_of_nonneg_left hh (by linarith)
      _ = 1 := e1
  linarith

/-! ### §8b — the SHARP group→algebra constant, and the small-field consumer form

`frobNorm_su2Log_le` (§8a) uses LEMMA L's `π/2`, which certifies only the per-bond threshold
`‖U − 1‖_F ≤ 2/π = 0.6366…` — narrower than the campaign's small-field class
`frobSupBond ≤ √2/2 = 0.7071…`. The sharp constant for `‖log g‖_F ≤ C‖g − 1‖_F` on the cap is
`θ/(2 sin(θ/2))|_{θ=π/2} = π/(2√2) = 1.1107…`, and getting it needs the chord bound for `sin` on
`[0, π/4]` (slope `2√2/π = 0.9003`), not Mathlib's `[0,π/2]` Jordan slope `2/π = 0.6366`. That
chord bound follows from `strictConcaveOn_sin_Icc`. With it, `‖U − 1‖_F ≤ √2/2` gives
`‖log U‖_F ≤ π/4`, so a PAIR lands at `π/2 = 1.5708 ≤ 2` — inside `bch2_frobNorm`'s domain. -/

/-- Chord bound: `sin x ≥ (2√2/π)·x` on `[0, π/4]`, from concavity of `sin` on `[0,π]`. -/
theorem chord_sin_quarter {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    2 * Real.sqrt 2 / Real.pi * x ≤ Real.sin x := by
  have hpi := Real.pi_pos
  have ht0 : (0:ℝ) ≤ 4 * x / Real.pi := by positivity
  have ht1 : 4 * x / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) Real.pi := Set.mem_Icc.mpr ⟨le_refl (0:ℝ), le_of_lt hpi⟩
  have h4 : (Real.pi / 4 : ℝ) ∈ Set.Icc (0:ℝ) Real.pi :=
    Set.mem_Icc.mpr ⟨by positivity, by linarith⟩
  have hcc := strictConcaveOn_sin_Icc.concaveOn.2 h0 h4
      (show (0:ℝ) ≤ 1 - 4 * x / Real.pi by linarith) ht0 (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add] at hcc
  have harg : 4 * x / Real.pi * (Real.pi / 4) = x := by field_simp
  rw [harg, Real.sin_pi_div_four] at hcc
  have hrw : 2 * Real.sqrt 2 / Real.pi * x = 4 * x / Real.pi * (Real.sqrt 2 / 2) := by
    field_simp; ring
  rw [hrw]
  exact hcc

/-- `‖g − 1‖²_F = 4(1 − cos θ(g))`. -/
theorem frobSq_su2_sub_one (g : SU2) :
    frobSq ((g : M2) - 1) = 4 * (1 - Real.cos (su2Angle g)) := by
  have hY : IsSu2 (Yof g) := isSu2_Yof g
  have hd : (g : M2) - 1 = (Real.cos (su2Angle g) - 1) • (1 : M2) + (1:ℝ) • Yof g := by
    rw [su2_decomp g, sub_smul, one_smul]
    module
  rw [hd, AdalyFormal.Balaban.ClassPropagationUbar.comb_frobSq hY.1 hY.2]
  have hq : frobSq (Yof g) = 2 * Real.sin (su2Angle g) ^ 2 := by
    have h := nu_sq (Yof g)
    rw [nu_Yof g] at h
    linarith
  rw [hq]
  nlinarith [Real.sin_sq_add_cos_sq (su2Angle g)]

/-- `‖g − 1‖_F ≤ 2` is EXACTLY the cap `θ(g) ≤ π/2` (this direction; `4(1−cos θ) ≤ 4 ↔ cos θ ≥ 0`).
So the consumer never has to carry an angle hypothesis. -/
theorem angle_le_of_frobNorm_sub_one {g : SU2} (h : frobNorm ((g : M2) - 1) ≤ 2) :
    su2Angle g ≤ Real.pi / 2 := by
  have hnn : 0 ≤ frobNorm ((g : M2) - 1) := frobNorm_nonneg _
  have hsq : frobSq ((g : M2) - 1) ≤ 4 := by
    have he : frobSq ((g : M2) - 1) = frobNorm ((g : M2) - 1) ^ 2 := by
      unfold frobNorm
      rw [Real.sq_sqrt (frobSq_nonneg _)]
    rw [he]; nlinarith
  rw [frobSq_su2_sub_one] at hsq
  have hc : 0 ≤ Real.cos (su2Angle g) := by linarith
  rw [cos_su2Angle] at hc
  rw [su2Angle]
  exact Real.arccos_le_pi_div_two.mpr hc

/-- `‖log g‖²_F = 2·θ(g)²` on the cap. -/
theorem frobSq_su2Log {g : SU2} (h : su2Angle g ≤ Real.pi / 2) :
    frobSq (su2Log g) = 2 * (su2Angle g) ^ 2 := by
  have hks := kappa_mul_sin h
  have hlog : su2Log g = (su2Kappa g) • Yof g := by
    rw [su2Log_eq_kappa_smul, real_smul_eq]
  rw [hlog, frobSq_smul]
  have hq : frobSq (Yof g) = 2 * Real.sin (su2Angle g) ^ 2 := by
    have hh := nu_sq (Yof g)
    rw [nu_Yof g] at hh
    linarith
  rw [hq]
  linear_combination (2 * (su2Kappa g * Real.sin (su2Angle g) + su2Angle g)) * hks

/-- **THE SHARP GROUP→ALGEBRA BOUND.** `‖log g‖_F ≤ (π/(2√2))·‖g − 1‖_F` on the cap.
`π/(2√2) = 1.1107…`, against `frobNorm_su2Log_le`'s `π/2 = 1.5708…`.

**What "SHARP" here refers to (added 2026-08-03; before that, nothing).** The word is now carried by
`h2prime_isLeast` in §9d: `π/(2√2)` is the LEAST constant for which this statement holds on the cap
`θ ≤ π/2`. It is ATTAINED at the pinned boundary element `sG` (`h2prime_attained_at_sG`), the
attainment is not at zero (`sG_sub_one_separated`), and no smaller constant works
(`h2prime_constant_lower`). Sharpness is for the cap AS STATED and for no smaller cap. -/
theorem frobNorm_su2Log_le_sharp {g : SU2} (h : su2Angle g ≤ Real.pi / 2) :
    frobNorm (su2Log g) ≤ (Real.pi / (2 * Real.sqrt 2)) * frobNorm ((g : M2) - 1) := by
  have hpi := Real.pi_pos
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hth0 : 0 ≤ su2Angle g := su2Angle_nonneg g
  refine frobNorm_le_of_frobSq_le (by positivity) ?_
  rw [frobSq_su2Log h, frobSq_su2_sub_one]
  -- half-angle and the chord bound
  have hhalf : Real.cos (su2Angle g) = 1 - 2 * Real.sin (su2Angle g / 2) ^ 2 := by
    have hc := Real.cos_two_mul (su2Angle g / 2)
    rw [show 2 * (su2Angle g / 2) = su2Angle g by ring] at hc
    nlinarith [Real.sin_sq_add_cos_sq (su2Angle g / 2)]
  have hchord : 2 * Real.sqrt 2 / Real.pi * (su2Angle g / 2) ≤ Real.sin (su2Angle g / 2) :=
    chord_sin_quarter (by linarith) (by linarith)
  have hnn : (0:ℝ) ≤ 2 * Real.sqrt 2 / Real.pi * (su2Angle g / 2) := by positivity
  have hsq : (2 * Real.sqrt 2 / Real.pi * (su2Angle g / 2)) ^ 2
      ≤ Real.sin (su2Angle g / 2) ^ 2 := by nlinarith [hchord, hnn]
  have hexp : (2 * Real.sqrt 2 / Real.pi * (su2Angle g / 2)) ^ 2
      = 2 * (su2Angle g) ^ 2 / Real.pi ^ 2 := by
    field_simp
    nlinarith [hss]
  rw [hexp] at hsq
  have hcsq : (Real.pi / (2 * Real.sqrt 2)) ^ 2 = Real.pi ^ 2 / 8 := by
    field_simp
    nlinarith [hss]
  rw [hcsq, hhalf]
  have hp2 : (0:ℝ) < Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ hp2] at hsq
  nlinarith [hsq, hp2]

/-- **BCH-2 IN THE CONSUMER'S OWN UNITS.** For `U, V ∈ SU(2)` with `‖U − 1‖_F, ‖V − 1‖_F ≤ √2/2`
— the campaign's small-field class, per bond —

`‖log(U·V) − (log U + log V)‖_F ≤ 7·‖log U‖_F·‖log V‖_F`.

No angle hypothesis and no `exp` appears: `angle_le_of_frobNorm_sub_one` supplies the cap and
`frobNorm_su2Log_le_sharp` supplies the domain, both from the group bound alone. -/
theorem bch2_group {U V : SU2}
    (hU : frobNorm ((U : M2) - 1) ≤ Real.sqrt 2 / 2)
    (hV : frobNorm ((V : M2) - 1) ≤ Real.sqrt 2 / 2) :
    frobNorm (su2Log (U * V) - (su2Log U + su2Log V))
      ≤ 7 * (frobNorm (su2Log U) * frobNorm (su2Log V)) := by
  have hpi := Real.pi_lt_d2
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2p : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hU2 : frobNorm ((U : M2) - 1) ≤ 2 := by linarith
  have hV2 : frobNorm ((V : M2) - 1) ≤ 2 := by linarith
  have hangU : su2Angle U ≤ Real.pi / 2 := angle_le_of_frobNorm_sub_one hU2
  have hangV : su2Angle V ≤ Real.pi / 2 := angle_le_of_frobNorm_sub_one hV2
  -- each log has norm at most pi/4
  have hquart : ∀ g : SU2, su2Angle g ≤ Real.pi / 2 →
      frobNorm ((g : M2) - 1) ≤ Real.sqrt 2 / 2 → frobNorm (su2Log g) ≤ Real.pi / 4 := by
    intro g hg hgb
    have h := frobNorm_su2Log_le_sharp hg
    have hc : (0:ℝ) ≤ Real.pi / (2 * Real.sqrt 2) := by positivity
    have h2 : (Real.pi / (2 * Real.sqrt 2)) * frobNorm ((g : M2) - 1)
        ≤ (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt 2 / 2) :=
      mul_le_mul_of_nonneg_left hgb hc
    have h3 : (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt 2 / 2) = Real.pi / 4 := by
      field_simp
      nlinarith [hss]
    linarith
  have hlU := hquart U hangU hU
  have hlV := hquart V hangV hV
  have hdom : frobNorm (su2Log U) + frobNorm (su2Log V) ≤ 2 := by linarith
  -- transport to the exp form
  have hUe : su2Exp (su2Log U) = U :=
    AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne U (ne_negOne_of_angle_le hangU)
  have hVe : su2Exp (su2Log V) = V :=
    AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne V (ne_negOne_of_angle_le hangV)
  have h := bch2_seven (isSu2_su2Log U) (isSu2_su2Log V) hdom
  rwa [hUe, hVe] at h

/-! ## §9 — W3: THE SHARPNESS OF LEMMA L's CONSTANT

**Why this section exists.** In the first revision of this lane, LEMMA L's docstring and `SCOPE.md`
asserted that `π/2` is SHARP, and the only evidence offered anywhere was a Python random-sampling
exploration. Under the REFORM CHARTER Python signs nothing, so the word was billed and not proved;
gate-1 prosecution convicted exactly that word (`compute/bch2_prosecution/VERDICT.md`, ruling 4b),
naming as its overturn condition *"a Lean theorem exhibiting a witness pair or limiting sequence for
the Lipschitz ratio approaching/exceeding `3/2`"*. This section is that theorem — and it is stronger
than the overturn condition asked for, because no limit is needed.

**The mechanism, in one line.** On the cap BOUNDARY `θ(g) = π/2` the logarithm is exactly a
rescaling: `cos θ = 0` kills the scalar part, so `Yof g = g`, and `κ = θ/sin θ = π/2`, whence
`log g = (π/2)·g`. Two boundary elements therefore satisfy LEMMA L with EQUALITY, whatever their
axes — the antipodal pair `(J, −J)` and the ORTHOGONAL pair `(J, K)` both attain it. The old
docstring's `W ∥ −W'` was not a necessary condition.

**Order of business.** (1) the boundary identity and the equality it forces; (2) a PINNED separated
boundary pair, so the equality is not `0 = 0`; (3) sharpness proper, in two forms — no smaller
constant works, and the `3/2` form is false; (4) a control that the inequality is STRICT strictly
inside the cap, so §9 is a statement about the boundary and not an identity in disguise;
(5) **§9d, added 2026-08-03 after the triple gate** — the same treatment for the OTHER constant this
file calls sharp, H2′'s `π/(2√2)`, which had the identical defect one level down: an adjective with
no declaration behind it.

Every witness is a `def`, never an `∃` over free data (S91). -/

/-- **THE BOUNDARY IDENTITY.** At `θ(g) = π/2` the logarithm is a pure rescaling: `log g = (π/2)·g`.
`cos(π/2) = 0` makes `Yof g = g`, and `κ(g) = (π/2)/sin(π/2) = π/2`. -/
theorem su2Log_eq_half_pi_smul {g : SU2} (h : su2Angle g = Real.pi / 2) :
    su2Log g = (Real.pi / 2) • (g : M2) := by
  have hY : Yof g = (g : M2) := by
    rw [Yof, h, Real.cos_pi_div_two]
    simp
  have hk : su2Kappa g = Real.pi / 2 := by
    rw [su2Kappa, h, Real.sin_pi_div_two, div_one]
  rw [su2Log_eq_kappa_smul g, hY, hk, real_smul_eq]

/-- **LEMMA L IS AN EQUALITY ON THE WHOLE BOUNDARY SPHERE.** For ANY two group elements of angle
exactly `π/2` — no condition relating their axes — `‖log g − log g'‖_F = (π/2)·‖g − g'‖_F`. -/
theorem su2Log_lipschitz_attained_on_boundary {g g' : SU2}
    (h : su2Angle g = Real.pi / 2) (h' : su2Angle g' = Real.pi / 2) :
    frobNorm (su2Log g - su2Log g')
      = (Real.pi / 2) * frobNorm ((g : M2) - (g' : M2)) := by
  rw [su2Log_eq_half_pi_smul h, su2Log_eq_half_pi_smul h', ← smul_sub, frobNorm_smul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2)]

/-! ### §9a — the pinned separated boundary pair `(J, −J)`

`su2Log_lipschitz_attained_on_boundary` alone could be an equality between two zeros (`g = g'`
satisfies it). The pair below is pinned, lies ON the boundary, and is genuinely separated. -/

/-- `(π/2)·J`, the algebra element whose exponential is `J` itself. -/
noncomputable def sA : M2 := (Real.pi / 2) • wJ

/-- `−(π/2)·J`. -/
noncomputable def sA' : M2 := (-(Real.pi / 2)) • wJ

theorem isSu2_sA : IsSu2 sA := isSu2_wJ.smul _
theorem isSu2_sA' : IsSu2 sA' := isSu2_wJ.smul _

theorem nu_sA : nu sA = Real.pi / 2 := by
  rw [sA]; exact nu_smul_wJ (by positivity)

theorem nu_sA' : nu sA' = Real.pi / 2 := by
  rw [sA', nu_smul, nu_wJ, mul_one, abs_of_nonpos (by linarith [Real.pi_pos])]
  ring

noncomputable def sG : SU2 := su2Exp sA
noncomputable def sG' : SU2 := su2Exp sA'

theorem angle_sG : su2Angle sG = Real.pi / 2 := by
  rw [sG, angle_exp isSu2_sA (by rw [nu_sA]; linarith [Real.pi_pos]), nu_sA]

theorem angle_sG' : su2Angle sG' = Real.pi / 2 := by
  rw [sG', angle_exp isSu2_sA' (by rw [nu_sA']; linarith [Real.pi_pos]), nu_sA']

theorem log_sG : su2Log sG = sA :=
  log_exp isSu2_sA (by rw [nu_sA]; linarith [Real.pi_pos])

theorem log_sG' : su2Log sG' = sA' :=
  log_exp isSu2_sA' (by rw [nu_sA']; linarith [Real.pi_pos])

/-- `exp((π/2)·J) = J` — the exponential lands exactly on the generator, because `cos(π/2) = 0`
and `sin(π/2)/(π/2) · (π/2) = 1`. -/
theorem coe_sG : ((sG : SU2) : M2) = wJ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [sG, exp_form isSu2_sA, nu_sA, Real.cos_pi_div_two, Real.sin_pi_div_two, sA, smul_smul]
  have h1 : (1 : ℝ) * (Real.pi / 2)⁻¹ * (Real.pi / 2) = 1 := by field_simp
  rw [h1, one_smul, zero_smul, zero_add]

/-- `exp(−(π/2)·J) = −J`. -/
theorem coe_sG' : ((sG' : SU2) : M2) = -wJ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [sG', exp_form isSu2_sA', nu_sA', Real.cos_pi_div_two, Real.sin_pi_div_two, sA', smul_smul]
  have h1 : (1 : ℝ) * (Real.pi / 2)⁻¹ * (-(Real.pi / 2)) = -1 := by field_simp
  rw [h1, zero_smul, zero_add, neg_one_smul]

theorem sharp_num : su2Log sG - su2Log sG' = Real.pi • wJ := by
  rw [log_sG, log_sG', sA, sA', ← sub_smul]
  congr 1
  ring

theorem sharp_den : ((sG : SU2) : M2) - ((sG' : SU2) : M2) = (2 : ℝ) • wJ := by
  rw [coe_sG, coe_sG']
  module

theorem frobNorm_sharp_num : frobNorm (su2Log sG - su2Log sG') = Real.pi * Real.sqrt 2 := by
  rw [sharp_num, frobNorm_smul, frobNorm_wJ, abs_of_nonneg Real.pi_pos.le]

theorem frobNorm_sharp_den :
    frobNorm (((sG : SU2) : M2) - ((sG' : SU2) : M2)) = 2 * Real.sqrt 2 := by
  rw [sharp_den, frobNorm_smul, frobNorm_wJ]
  norm_num

/-- **W3a — THE BOUND IS ATTAINED, EXACTLY, AT A PINNED PAIR.** `π√2 = (π/2)·2√2`. -/
theorem su2Log_lipschitz_attained :
    frobNorm (su2Log sG - su2Log sG')
      = (Real.pi / 2) * frobNorm (((sG : SU2) : M2) - ((sG' : SU2) : M2)) := by
  rw [frobNorm_sharp_num, frobNorm_sharp_den]
  ring

/-- **W3b — AND IT IS NOT `0 = 0`.** The witness pair is separated: `‖g − g'‖_F = 2√2 > 0`. -/
theorem sharp_pair_separated : 0 < frobNorm (((sG : SU2) : M2) - ((sG' : SU2) : M2)) := by
  rw [frobNorm_sharp_den]
  have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-! ### §9b — sharpness proper -/

/-- **W3c — NO SMALLER CONSTANT WORKS.** Any `c` that makes `su2Log` `c`-Lipschitz on the cap
satisfies `π/2 ≤ c`. The proof is one instantiation at the pinned pair; the pair's SEPARATION
(`sharp_pair_separated`) is what makes the instantiation informative. -/
theorem su2Log_lipschitz_constant_sharp {c : ℝ}
    (h : ∀ g g' : SU2, su2Angle g ≤ Real.pi / 2 → su2Angle g' ≤ Real.pi / 2 →
      frobNorm (su2Log g - su2Log g') ≤ c * frobNorm ((g : M2) - (g' : M2))) :
    Real.pi / 2 ≤ c := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hw := h sG sG' (le_of_eq angle_sG) (le_of_eq angle_sG')
  rw [frobNorm_sharp_num, frobNorm_sharp_den] at hw
  nlinarith [hw, hs2]

/-- **W3d — SHARPNESS, IN THE CANONICAL FORM.** `π/2` is the LEAST real constant for which
`su2Log` is Lipschitz on the cap. Membership is LEMMA L; the lower bound is `W3c`. THIS is the
declaration the word "SHARP" refers to. -/
theorem su2Log_lipschitz_isLeast :
    IsLeast {c : ℝ | ∀ g g' : SU2, su2Angle g ≤ Real.pi / 2 → su2Angle g' ≤ Real.pi / 2 →
        frobNorm (su2Log g - su2Log g') ≤ c * frobNorm ((g : M2) - (g' : M2))} (Real.pi / 2) :=
  ⟨fun _ _ hg hg' => su2Log_lipschitz hg hg', fun _ hc => su2Log_lipschitz_constant_sharp hc⟩

/-- **W3e — THE `3/2` FORM IS FALSE.** This is exactly the statement mutation `M3` produces, in
explicit-binder form: `3/2 < π/2`, so no proof of it can exist. Before §9 existed, `M3`'s
classification as a FALSITY test rested on Python numerics; it now rests on this declaration. -/
theorem su2Log_not_lipschitz_three_halves :
    ¬ (∀ g g' : SU2, su2Angle g ≤ Real.pi / 2 → su2Angle g' ≤ Real.pi / 2 →
      frobNorm (su2Log g - su2Log g') ≤ (3 / 2 : ℝ) * frobNorm ((g : M2) - (g' : M2))) := by
  intro h
  have := su2Log_lipschitz_constant_sharp h
  linarith [Real.pi_gt_three]

/-! ### §9b′ — the ORTHOGONAL boundary pair `(J, K)` attains it too

S1 has no condition relating the axes, so the attainment is not about antipodality. This is the
instance that says so out loud, because the LEMMA L docstring asserts it: `K = [[0,1],[−1,0]]` is
orthogonal to `J` in the Frobenius inner product (`ip wJ wK = 0`), both have angle `π/2`, and the
ratio is again exactly `π/2` — here as `π = (π/2)·2`. The old docstring's condition `W ∥ −W'` was
therefore not necessary, and this pair is the counterexample to its necessity. -/

noncomputable def sB : M2 := (Real.pi / 2) • wK

theorem isSu2_sB : IsSu2 sB := isSu2_wK.smul _

theorem nu_sB : nu sB = Real.pi / 2 := by
  rw [sB]; exact nu_smul_wK (by positivity)

noncomputable def sK : SU2 := su2Exp sB

theorem angle_sK : su2Angle sK = Real.pi / 2 := by
  rw [sK, angle_exp isSu2_sB (by rw [nu_sB]; linarith [Real.pi_pos]), nu_sB]

/-- `exp((π/2)·K) = K`, the same collapse as `coe_sG` on the other generator. -/
theorem coe_sK : ((sK : SU2) : M2) = wK := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [sK, exp_form isSu2_sB, nu_sB, Real.cos_pi_div_two, Real.sin_pi_div_two, sB, smul_smul]
  have h1 : (1 : ℝ) * (Real.pi / 2)⁻¹ * (Real.pi / 2) = 1 := by field_simp
  rw [h1, one_smul, zero_smul, zero_add]

/-- `‖J − K‖_F = 2`: the cross term vanishes because `ip wJ wK = 0`. -/
theorem frobNorm_orth_den :
    frobNorm (((sG : SU2) : M2) - ((sK : SU2) : M2)) = 2 := by
  have h : frobSq (wJ - wK) = 4 := by
    rw [frobSq_sub, frobSq_wJ, frobSq_wK]
    have : ip wJ wK = 0 := by
      simp [ip, wJ, wK, Matrix.of_apply]
    rw [this]; ring
  rw [coe_sG, coe_sK, frobNorm, h]
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **W3a′ — ATTAINED ON AN ORTHOGONAL PAIR.** No antipodality anywhere. -/
theorem su2Log_lipschitz_attained_orthogonal :
    frobNorm (su2Log sG - su2Log sK)
      = (Real.pi / 2) * frobNorm (((sG : SU2) : M2) - ((sK : SU2) : M2)) :=
  su2Log_lipschitz_attained_on_boundary angle_sG angle_sK

theorem orth_pair_separated : 0 < frobNorm (((sG : SU2) : M2) - ((sK : SU2) : M2)) := by
  rw [frobNorm_orth_den]; norm_num

/-- The two sides in numbers: `π = (π/2)·2`. -/
theorem frobNorm_orth_num : frobNorm (su2Log sG - su2Log sK) = Real.pi := by
  rw [su2Log_lipschitz_attained_orthogonal, frobNorm_orth_den]; ring

/-! ### §9c — the control: the inequality is STRICT inside the cap

Without this, §9 would be compatible with `‖log g − log g'‖_F = (π/2)‖g − g'‖_F` holding
identically on the cap, which is FALSE. The pinned interior pair `exp(±(π/4)·J)` has angle `π/4`
and ratio `π√2/4 = 1.1107… < π/2`. -/

noncomputable def iA : M2 := (Real.pi / 4) • wJ
noncomputable def iA' : M2 := (-(Real.pi / 4)) • wJ

theorem isSu2_iA : IsSu2 iA := isSu2_wJ.smul _
theorem isSu2_iA' : IsSu2 iA' := isSu2_wJ.smul _

theorem nu_iA : nu iA = Real.pi / 4 := by
  rw [iA]; exact nu_smul_wJ (by positivity)

theorem nu_iA' : nu iA' = Real.pi / 4 := by
  rw [iA', nu_smul, nu_wJ, mul_one, abs_of_nonpos (by linarith [Real.pi_pos])]
  ring

noncomputable def iG : SU2 := su2Exp iA
noncomputable def iG' : SU2 := su2Exp iA'

/-- The interior pair is STRICTLY inside the cap: angle `π/4 < π/2`. -/
theorem angle_iG : su2Angle iG = Real.pi / 4 := by
  rw [iG, angle_exp isSu2_iA (by rw [nu_iA]; linarith [Real.pi_pos]), nu_iA]

theorem angle_iG' : su2Angle iG' = Real.pi / 4 := by
  rw [iG', angle_exp isSu2_iA' (by rw [nu_iA']; linarith [Real.pi_pos]), nu_iA']

theorem log_iG_sub : su2Log iG - su2Log iG' = (Real.pi / 2) • wJ := by
  rw [iG, iG', log_exp isSu2_iA (by rw [nu_iA]; linarith [Real.pi_pos]),
    log_exp isSu2_iA' (by rw [nu_iA']; linarith [Real.pi_pos]), iA, iA', ← sub_smul]
  congr 1
  ring

/-- `exp((π/4)J) − exp(−(π/4)J) = 2 sin(π/4)·J = √2·J`: the scalar parts cancel. -/
theorem coe_iG_sub :
    ((iG : SU2) : M2) - ((iG' : SU2) : M2) = (Real.sqrt 2) • wJ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [iG, iG', exp_form isSu2_iA, exp_form isSu2_iA', nu_iA, nu_iA', iA, iA',
    smul_smul, smul_smul]
  have h1 : Real.sin (Real.pi / 4) * (Real.pi / 4)⁻¹ * (Real.pi / 4)
      = Real.sqrt 2 / 2 := by
    rw [Real.sin_pi_div_four]; field_simp
  have h2 : Real.sin (Real.pi / 4) * (Real.pi / 4)⁻¹ * (-(Real.pi / 4))
      = -(Real.sqrt 2 / 2) := by
    rw [Real.sin_pi_div_four]; field_simp
  rw [h1, h2]
  module

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2, h]

/-- **W3f — STRICT INSIDE THE CAP.** At `θ = π/4` the ratio is `π√2/4 < π/2`, so LEMMA L is a
genuine inequality and `su2Log_lipschitz_attained_on_boundary` is a statement about the BOUNDARY,
not an identity in disguise. -/
theorem lipschitz_strict_inside :
    frobNorm (su2Log iG - su2Log iG')
      < (Real.pi / 2) * frobNorm (((iG : SU2) : M2) - ((iG' : SU2) : M2)) := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hL : frobNorm (su2Log iG - su2Log iG') = Real.pi / 2 * Real.sqrt 2 := by
    rw [log_iG_sub, frobNorm_smul, frobNorm_wJ, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi/2)]
  have hR : frobNorm (((iG : SU2) : M2) - ((iG' : SU2) : M2)) = 2 := by
    rw [coe_iG_sub, frobNorm_smul, frobNorm_wJ, abs_of_nonneg hs2.le, hss]
  rw [hL, hR]
  nlinarith [sqrt_two_lt_two, Real.pi_pos]

/-! ### §9d — THE SAME TREATMENT FOR H2′'s CONSTANT `π/(2√2)`

**Why this subsection exists, and who raised it.** §9a–§9c put LEMMA L's word SHARP behind a named
declaration (`su2Log_lipschitz_isLeast`). H2′ — `frobNorm_su2Log_le_sharp`, §8b — was still billed
**SHARP** in its own docstring (`THE SHARP GROUP→ALGEBRA BOUND`) and in `SCOPE.md` rows 28/133/378,
on the strength of the two constituent formulas `frobSq_su2Log` and `frobSq_su2_sub_one`, with NO
attainment, lower-bound or `IsLeast` declaration anywhere in this file. That is the same defect
class that convicted LEMMA L's SHARP at gate 1, one level down, and the Sol gate raised it:
`compute/sol_bch2/VERDICT.md` §A3 ("sharp-occurrence filing gap") and `compute/sol_bch22/VERDICT.md`
§A3 item 1. It is non-load-bearing for the inequalities — `bch2_group` (H3) consumes only H2′'s
UPPER bound — but a sharp adjective with no declaration name is exactly what this lane was
convicted for, so it is closed here rather than filed.

**Credit.** The two statements `h2prime_attained_at_sG` and `h2prime_constant_lower` are DUE TO THE
SOL GATE (`compute/sol_bch2/Bch2Probes.lean:236` and `:246`, compiled there against this lane's
`Bch2.olean`); they are re-derived here inside the exhibit, against this file's own `log_sG`,
`frobSq_su2_sub_one`, `frobNorm_smul` and `frobNorm_wJ`. `h2prime_isLeast` is the canonical form and
is added here.

**The mechanism, in one line.** No new witness is introduced: the element is the SAME pinned
boundary element `sG = exp((π/2)·J) = J` that §9a already uses. At `θ(sG) = π/2`,
`‖log sG‖_F = (π/2)·√2` (from `log_sG` and `‖J‖_F = √2`) while `‖sG − 1‖_F = 2` (from
`‖g − 1‖²_F = 4(1 − cos θ)` at `cos(π/2) = 0`), and `(π/2)·√2 = (π/(2√2))·2` exactly.

**And it is not `0 = 0`.** `sG_sub_one_separated` records `‖sG − 1‖_F = 2 > 0`. Without it the
instantiation inside `h2prime_constant_lower` would read `0 ≤ c·0` and bound `c` not at all — the
same S82-style trap that `sharp_pair_separated` guards in §9a, and that mutation `M21` fires on. -/

/-- `‖sG − 1‖_F = 2`: at `θ = π/2`, `‖g − 1‖²_F = 4(1 − cos θ) = 4`. -/
theorem frobNorm_sG_sub_one : frobNorm (((sG : SU2) : M2) - 1) = 2 := by
  unfold frobNorm
  rw [frobSq_su2_sub_one, angle_sG, Real.cos_pi_div_two,
    show (4:ℝ) * (1 - 0) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **H2′ IS NOT AN ATTAINMENT AT ZERO.** The witness is separated from the identity. -/
theorem sG_sub_one_separated : 0 < frobNorm (((sG : SU2) : M2) - 1) := by
  rw [frobNorm_sG_sub_one]; norm_num

/-- `‖log sG‖_F = (π/2)·√2`, from `log sG = (π/2)·J` (`log_sG`) and `‖J‖_F = √2`. -/
theorem frobNorm_log_sG : frobNorm (su2Log sG) = (Real.pi / 2) * Real.sqrt 2 := by
  rw [log_sG, sA, frobNorm_smul, frobNorm_wJ,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

/-- **H2′a — THE CONSTANT IS ATTAINED, EXACTLY, AT THE PINNED BOUNDARY ELEMENT.**
`(π/2)·√2 = (π/(2√2))·2`. Statement due to the Sol gate (`compute/sol_bch2/Bch2Probes.lean:236`,
`h2prime_attained_at_sG`); re-derived here. -/
theorem h2prime_attained_at_sG :
    frobNorm (su2Log sG) =
      (Real.pi / (2 * Real.sqrt 2)) * frobNorm (((sG : SU2) : M2) - 1) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [frobNorm_log_sG, frobNorm_sG_sub_one]
  field_simp
  nlinarith [hss]

/-- **H2′b — NO SMALLER CONSTANT WORKS.** Any `c` for which `‖log g‖_F ≤ c‖g − 1‖_F` holds on the
whole cap satisfies `π/(2√2) ≤ c`. One instantiation at `sG`; `sG_sub_one_separated` is what makes
it informative. Statement due to the Sol gate (`compute/sol_bch2/Bch2Probes.lean:246`,
`h2prime_constant_lower`); re-derived here. -/
theorem h2prime_constant_lower {c : ℝ}
    (h : ∀ g : SU2, su2Angle g ≤ Real.pi / 2 →
      frobNorm (su2Log g) ≤ c * frobNorm ((g : M2) - 1)) :
    Real.pi / (2 * Real.sqrt 2) ≤ c := by
  have hw := h sG (le_of_eq angle_sG)
  rw [h2prime_attained_at_sG, frobNorm_sG_sub_one] at hw
  linarith

/-- **H2′c — SHARPNESS, IN THE CANONICAL FORM.** `π/(2√2)` is the LEAST real constant for which the
group→algebra bound holds on the cap `θ ≤ π/2`. Membership is `frobNorm_su2Log_le_sharp` (H2′); the
lower bound is `h2prime_constant_lower`. THIS is the declaration the word "SHARP" in H2′'s docstring
and in `SCOPE.md` rows 28/133/378 refers to — the exact analogue of `su2Log_lipschitz_isLeast` for
LEMMA L. As there, the sharpness is for the cap `θ ≤ π/2` AS STATED: the witness lies exactly ON the
boundary, and a smaller cap admits a smaller constant. -/
theorem h2prime_isLeast :
    IsLeast {c : ℝ | ∀ g : SU2, su2Angle g ≤ Real.pi / 2 →
        frobNorm (su2Log g) ≤ c * frobNorm ((g : M2) - 1)} (Real.pi / (2 * Real.sqrt 2)) :=
  ⟨fun _ hg => frobNorm_su2Log_le_sharp hg, fun _ hc => h2prime_constant_lower hc⟩

end AdalyFormal.Balaban.Bch2
