/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SuTwoLogExpFaithful
import AdalyFormal.Balaban.RegularUQChain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `BlockingLinkEstimate.lean` — the link recursion DERIVED from CMP98 (43)

`GammaLevelDefect.lean` carries a hypothesis

  `hlink : ∀ l, l < k → eps (l + 1) ≤ ell * eps l + Kb * beta l`

labelled "CMP98 (43): the blocking step, `Kb` the source `O(1)`". **(43) is not that.** Read off
the page image `compute/kuniform_cr/renders/CMP98_pdf8-08.png` (printed p.24), verbatim:

> `Ū_c^{k+1} = (Ū^k)‾_c = exp[i Σ_{x∈B(c₋)} L^{−d} (1/i) log Ū^k(Γ_{c,x})(Ū^k(c))^{−1}] Ū^k(c),`
> `c ⊂ Ω^{(k+1)}`  (43)

an exact **group-valued definition**. No `Kb`, no scalar recursion, no `ε`. This module derives the
recursion from the definition, and produces `Kb`.

## The answer

    ‖Ū_c − 1‖  ≤  L·ε  +  (π/2)·N(d,L)·β ,     N(d,L) = (d−1)·L·(L−1) + C(d,2)·(L−1)²

with `ε` the level-`k` link defect and `β` the level-`k` plaquette curvature, both taken over the
box spanned by `B(c₋) ∪ B(c₊)`. So

* the coefficient of `ε` is **exactly `L`** — not `O(L)`;
* `Kb(d,L) = (π/2)·N(d,L)` is an **explicit function of `(d,L)` alone**;
* **`Kb` carries NO level index.** Every ingredient is either the block geometry — identical at
  every RG step, since (43) applies the one-step operation (42) to the field on `Ω^{(k)}` — or a
  universal `SU(2)` constant. Hence `sup_l Kb l = Kb(d,L) < ∞` trivially, and the `hlink` shape
  with ONE `Kb` for all levels is the honest form, not a strengthening.

Values: `d=3,L=2 → N=7, Kb=7π/2≈10.996`; `d=3,L=3 → N=24, Kb=12π≈37.699`;
`d=4,L=2 → N=12, Kb=6π≈18.850`.

## The five steps

Write (43) as `Ū_c = exp(H)·U(c)`, `H = Σ_{x∈B(c₋)} L^{−d}·log W_x`, `W_x = U(Γ_{c,x})U(c)^{−1}`.
(Balaban's `exp[i·Σ w·(1/i)log(·)]` is `exp[Σ w·log(·)]`: the `i` and `1/i` cancel exactly, and this
tree's `su2Log` IS Balaban's `log` — `su2Log (torus t) = diag(it,−it)`, i.e. `iA` with `A` hermitian,
matching (23). No convention gap.)

S1 `‖Ū_c − 1‖ ≤ ‖exp H − 1‖ + ‖U(c) − 1‖`      — `RegularUQChain.frobNorm_su_mul_sub_one_le`
S2 `‖U(c) − 1‖ ≤ L·ε`                          — `c` is `L` fine bonds; telescoping. Coefficient `L`.
S3 `‖exp H − 1‖ ≤ ‖H‖ ≤ max_x ‖log W_x‖`       — CMP98 (24) + the weights `L^{−d}` sum to `1`
                                                 over the `L^d` points of `B(c₋)`
S4 `‖log W_x‖ ≤ (π/2)‖W_x − 1‖`                — **CMP98 (25), printed p.21, re-derived here**
S5 `‖W_x − 1‖ ≤ N(d,L)·β`                      — `W_x` is a CLOSED-LOOP holonomy: a product of
                                                 `N` conjugated plaquettes (§6)

## Smallness: NONE needed for S1–S5. What IS needed, named

Balaban's own p.21 (23)/(25) make the logarithm **total** on unitaries (branch `arg ∈ ]−π,π]`) and
(25) **unconditional**. The source's "for `L²α₀` sufficiently small" (p.25) is needed for his
LINEARISATION `V̄_{0,c} = exp[iΣL^{−d}A(Γ_{c,x}) + O((L²α₀)²)]`, which the sharp constant `L²` in
(51) requires; a one-sided norm bound does not. What this module does carry explicitly:

* **`hbranch`** (§5): `su2Log (su2Exp H) = H`, the principal-branch condition. This is Lean-side
  bookkeeping forced by `SuTwoLogExpCore.su2Log`'s disclosed junk value at `g = −1`
  (`su2Log su2NegOne = 0`, `su2Exp 0 = 1 ≠ −1`). **§8 DISCHARGES it**, so it is not an extra
  assumption: `branch_of_frobNorm_lt` proves `‖H‖_F < √2·π ⟹ hbranch` by an explicit `SU(2)`
  diagonalisation, and §5 already bounds `‖H‖_F ≤ (π/2)·N·β`, so the sufficient condition is
  `N(d,L)·β < 2√2` — an INPUT bound on the curvature, and exactly the quantified form of the
  source's unquantified "for `L²α₀` sufficiently small". `2√2` is the maximum of `‖g−1‖_F` on
  `SU(2)`, attained only at `g = −1`: the condition says the loop holonomies do not reach the
  antipode. See `blockedLink_sub_one_le_of_curvature` and `link_recursion_of_curvature`.
* **a LOCALITY hypothesis, not a smallness one**: `β` must dominate the plaquettes of the box
  spanned by `B(c₋) ∪ B(c₊)`. That is exactly the region CMP98 p.24 names — "this definition is
  local in the sense that `Ū_c^k` depends only on the bond variables `U_b` for
  `b ⊂ B^k(c₋) ∪ B^k(c₊)`" (image-verified, p.24).

## Source pinning

* (43) — image `compute/kuniform_cr/renders/CMP98_pdf8-08.png`, printed p.24. Image-verified.
* **the DEFINITION of `Γ_{c,x}` is on p.19, not p.24.** CMP98 p.19, prose under (14):
  "Let us notice that `Γ_{c₋,x} ∪ [x, x(c)] ∪ Γ_{x(c),c₊}` is an oriented contour with `c₋` as an
  initial point and `c₊` as a final point. We denote it by `Γ_{c,x}`."
  **This page is ADJUDICATED ground truth**, not a machine draft: `corpus/pages/CMP98_p19.md`
  carries `verification_status: adjudicated` (2026-07-19, dual-read, adjudication on disk at
  `corpus/mathpix/diffs/CMP98_p19.ADJUDICATION.md`), and its `VERBATIM` section carries this
  sentence character-for-character. Same for `corpus/pages/CMP98_p24.md`.
* (24),(25) — CMP98 p.21 (`.../normalized/p21.md`, machine-draft layer):
  `|U − 1| ≤ max_j |λ_j| = |log U|` (24); `|log U| ≤ (π/2)|U − 1|` (25). §3/§4 below RE-DERIVE both
  in `frobNorm`; nothing is taken on the transcription's word.
* the axial-gauge consequence, image-verified verbatim and **SPANNING TWO PAGES**. Printed p.24
  ends mid-formula: "The conditions `V₀(Γ_{y,x}) = 1` imply `V₀(x,x+e₁) = 1`,
  `|V₀(x,x+e₂)−1| < |x₁−y₁|α₀`, `|V₀(x,x+e₃)−1| < (|x₁−y₁|+|x₂−y₂|)α₀`, …,
  `|V₀(x,x+e_μ)−1| < (|x₁−y₁|+…`" — and the completion is the FIRST LINE of printed p.25:
  "`+|x_{μ−1}−y_{μ−1}|)α₀, μ = 2, …, d`, for `x` in the neighborhood of `y`". Both halves were read
  at the page images (`CMP98_pdf8-08.png` and `CMP98_pdf9-09.png`). The general-`μ` term is
  therefore image-verified, but only across the page break — do not cite it as a p.24 quote.
  This printed statement IS §6's one-bond lasso count, and it pins the staircase coordinate order
  (direction `1` LAST, hence `0` plaquettes at `μ = 1`). `lassoCount_dir_one`, `_two`, `_three`
  below are the three LITERALLY PRINTED cases as theorems; no proof here uses the general-`μ`
  completion.
* CMP98 p.25, image-verified: `|Γ_{c,x}| < (2d+1)L`. Independent count from the p.19 definition:
  `d(L−1) + L + d(L−1) = (2d+1)L − 2d < (2d+1)L`. **Matches.** (`gammaPathLength_le`, §6b.)

## Scope honesty — what is proved here and what is not

PROVED (kernel, `sorry`-free): S1–S4 in full; the averaging; the assembly; the counting arithmetic
of §6; the level-uniform recursion of §7 with ONE `Kb` in the type; the `SU(2)` diagonalisation and
the branch discharge of §8; the conjugation isometry and the abstract Stokes telescoping of §9
(`frobNorm_conjProd_sub_one_le`, `loop_bound_of_surface`); the non-degeneracy control of §10.

~~NOT PROVED HERE — ONE residual, §11: the lattice-geometric half of S5, that the loop
`Γ_{c,x} ∪ (−c)` HAS a spanning surface with `surfCount ell x μ` plaquettes. §6 derives the COUNT
from the p.19 definition of `Γ_{c,x}`, §9 proves that such a product obeys the bound; what is not
built is the lattice, its paths, and the explicit surface. `loop_is_conj_plaquette_product` is that
step as a `sorry` with a name and a locator.~~ **SUPERSEDED 2026-07-29: THE RESIDUAL IS CLOSED.**
§11 now builds the lattice, its signed paths, the plaquette, the deformation algebra (§11h) and the
explicit surface, and `loop_is_conj_plaquette_product` is a theorem with NO `sorry`: the module
contains no `sorry` at all and `#print axioms` shows `[propext, Classical.choice, Quot.sound]` on
every declaration including that one. The count comes out EXACTLY `surfCount = cylCount + revCount`
(`pcL_finRange_eq_revCount`, `cyl_sum_eq_cylCount`).

Still true, and still the reason nothing downstream moved yet: **the identity is imported by nothing
and used by nothing.** `blockedLink_sub_one_le`, `blockedLink_sub_one_le_of_curvature`,
`link_recursion_of_blocking` and `link_recursion_of_curvature` all take S5 as an explicit
HYPOTHESIS about an abstract `loopHol`/`plaqAt`, not about `pathHol`/`plaqHol` of a configuration,
so discharging those hypotheses from this theorem is a separate (and now unblocked) wiring step.
-/

namespace AdalyFormal.Balaban.BlockingLinkEstimate

open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.RMapLipschitz

open scoped Matrix

/-! ## §1 — `frobNorm` is a genuine norm (triangle inequality, homogeneity, finite sums)

`frobSq`/`frobNorm` are plain real-valued functions with no norm typeclass (deliberately, per
`RMapLipschitz.lean`'s instance-diamond note). The three facts §5 needs are obtained by exhibiting
`frobNorm` as the `EuclideanSpace ℂ (Fin 4)` norm of the entry vector — no new instance on
`Matrix (Fin 2) (Fin 2) ℂ` is introduced, so the diamond is untouched. -/

/-- The entry vector of a `2×2` complex matrix, in `ℓ²`. -/
noncomputable def toVec (M : M2) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 ![M 0 0, M 0 1, M 1 0, M 1 1]

theorem frobNorm_eq_norm_toVec (M : M2) : frobNorm M = ‖toVec M‖ := by
  rw [EuclideanSpace.norm_eq, frobNorm]
  congr 1
  rw [Fin.sum_univ_four]
  simp only [toVec, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  rw [frobSq]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]

theorem toVec_add (M N : M2) : toVec (M + N) = toVec M + toVec N := by
  ext i
  fin_cases i <;> simp [toVec]

theorem toVec_smul (c : ℂ) (M : M2) : toVec (c • M) = c • toVec M := by
  ext i
  fin_cases i <;> simp [toVec]

theorem toVec_zero : toVec (0 : M2) = 0 := by
  ext i
  fin_cases i <;> simp [toVec]

theorem frobNorm_add_le (M N : M2) : frobNorm (M + N) ≤ frobNorm M + frobNorm N := by
  rw [frobNorm_eq_norm_toVec, frobNorm_eq_norm_toVec, frobNorm_eq_norm_toVec, toVec_add]
  exact norm_add_le _ _

theorem frobNorm_real_smul (c : ℝ) (M : M2) :
    frobNorm ((c : ℂ) • M) = |c| * frobNorm M := by
  rw [frobNorm_eq_norm_toVec, frobNorm_eq_norm_toVec, toVec_smul, norm_smul]
  simp

/-- Finite-sum triangle inequality for `frobNorm`. -/
theorem frobNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → M2) :
    frobNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, frobNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frobNorm_eq_norm_toVec, toVec_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (frobNorm_add_le _ _) (by linarith)

/-! ## §2 — the `SU(2)` angle bridges

Two exact identities, both elementary `2×2` algebra:

  `frobSq (g − 1)  = 4 − 2·Re tr g = 8 sin²(θ/2)`,   `frobSq (g − gᴴ) = 8 sin² θ`,   `θ = su2Angle g`.
-/

theorem trace_re_eq (g : SU2) : (Matrix.trace (g : M2)).re = 2 * ((g : M2) 0 0).re := by
  rw [Matrix.trace_fin_two, su2_e11 g]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

theorem normSq_re_im (z : ℂ) : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
  simp [Complex.normSq_apply]; ring

theorem re_e00_sq_le_one (g : SU2) : ((g : M2) 0 0).re ^ 2 ≤ 1 := by
  have h := su2_normSq g
  have h1 := Complex.normSq_nonneg ((g : M2) 0 1)
  have h2 : Complex.normSq ((g : M2) 0 0)
      = ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2 := normSq_re_im _
  nlinarith [sq_nonneg ((g : M2) 0 0).im]

theorem trace_re_div_two_le_one (g : SU2) : (Matrix.trace (g : M2)).re / 2 ≤ 1 := by
  have h := re_e00_sq_le_one g
  have ht := trace_re_eq g
  nlinarith

theorem neg_one_le_trace_re_div_two (g : SU2) : -1 ≤ (Matrix.trace (g : M2)).re / 2 := by
  have h := re_e00_sq_le_one g
  have ht := trace_re_eq g
  nlinarith

/-- `cos θ(g) = Re tr g / 2`. -/
theorem cos_su2Angle (g : SU2) : Real.cos (su2Angle g) = (Matrix.trace (g : M2)).re / 2 :=
  Real.cos_arccos (neg_one_le_trace_re_div_two g) (trace_re_div_two_le_one g)

theorem sin_half_su2Angle_nonneg (g : SU2) : 0 ≤ Real.sin (su2Angle g / 2) := by
  obtain ⟨hlo, hhi⟩ := su2Angle_mem g
  apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [Real.pi_pos]

theorem sin_su2Angle_nonneg (g : SU2) : 0 ≤ Real.sin (su2Angle g) := by
  obtain ⟨hlo, hhi⟩ := su2Angle_mem g
  exact Real.sin_nonneg_of_nonneg_of_le_pi hlo hhi

/-- **`frobSq (g − 1) = 4 − 2·Re tr g`** — exact, for every `g ∈ SU(2)`. -/
theorem frobSq_sub_one_eq (g : SU2) :
    frobSq ((g : M2) - 1) = 4 - 2 * (Matrix.trace (g : M2)).re := by
  have h11 := su2_e11 g
  have h10 := su2_e10 g
  have hns := su2_normSq g
  have ht := trace_re_eq g
  have e00 : ((g : M2) - 1) 0 0 = (g : M2) 0 0 - 1 := by
    simp [Matrix.sub_apply, Matrix.one_apply_eq]
  have e01 : ((g : M2) - 1) 0 1 = (g : M2) 0 1 := by
    simp [Matrix.sub_apply, Matrix.one_apply_ne]
  have e10 : ((g : M2) - 1) 1 0 = (g : M2) 1 0 := by
    simp [Matrix.sub_apply, Matrix.one_apply_ne]
  have e11 : ((g : M2) - 1) 1 1 = (g : M2) 1 1 - 1 := by
    simp [Matrix.sub_apply, Matrix.one_apply_eq]
  rw [frobSq, e00, e01, e10, e11, h11, h10]
  simp only [normSq_re_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  have hns' : ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2
      + (((g : M2) 0 1).re ^ 2 + ((g : M2) 0 1).im ^ 2) = 1 := by
    rw [← normSq_re_im, ← normSq_re_im]; exact hns
  nlinarith [hns', ht]

/-- `frobSq (g − 1) = 8 sin²(θ/2)`. -/
theorem frobSq_sub_one_angle (g : SU2) :
    frobSq ((g : M2) - 1) = 8 * Real.sin (su2Angle g / 2) ^ 2 := by
  have hc := cos_su2Angle g
  have hd : Real.cos (2 * (su2Angle g / 2)) = 1 - 2 * Real.sin (su2Angle g / 2) ^ 2 := by
    rw [Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (su2Angle g / 2)
    nlinarith [this]
  have hhalf : (2 : ℝ) * (su2Angle g / 2) = su2Angle g := by ring
  rw [hhalf] at hd
  rw [frobSq_sub_one_eq]
  nlinarith [hc, hd]

/-- **`‖g − 1‖_F = 2√2·sin(θ/2)`.** -/
theorem frobNorm_sub_one_eq (g : SU2) :
    frobNorm ((g : M2) - 1) = 2 * Real.sqrt 2 * Real.sin (su2Angle g / 2) := by
  have hs := sin_half_su2Angle_nonneg g
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ 2 * Real.sqrt 2 * Real.sin (su2Angle g / 2) := by
    have := Real.sqrt_nonneg 2; positivity
  rw [frobNorm, frobSq_sub_one_angle]
  have : (8 : ℝ) * Real.sin (su2Angle g / 2) ^ 2
      = (2 * Real.sqrt 2 * Real.sin (su2Angle g / 2)) ^ 2 := by
    rw [mul_pow, mul_pow]; rw [h2]; ring
  rw [this, Real.sqrt_sq hnn]

/-- `frobSq (g − gᴴ) = 8 sin² θ`. -/
theorem frobSq_sub_conjTranspose (g : SU2) :
    frobSq ((g : M2) - (g : M2)ᴴ) = 8 * Real.sin (su2Angle g) ^ 2 := by
  have hadj := su2_conjTranspose_eq_adjugate g
  have h11 := su2_e11 g
  have h10 := su2_e10 g
  have hns := su2_normSq g
  have hc := cos_su2Angle g
  have ht := trace_re_eq g
  have e00 : ((g : M2) - (g : M2)ᴴ) 0 0 = (g : M2) 0 0 - (g : M2) 1 1 := by
    rw [Matrix.sub_apply, hadj]; simp
  have e01 : ((g : M2) - (g : M2)ᴴ) 0 1 = (g : M2) 0 1 + (g : M2) 0 1 := by
    rw [Matrix.sub_apply, hadj]; simp
  have e10 : ((g : M2) - (g : M2)ᴴ) 1 0 = (g : M2) 1 0 + (g : M2) 1 0 := by
    rw [Matrix.sub_apply, hadj]; simp
  have e11 : ((g : M2) - (g : M2)ᴴ) 1 1 = (g : M2) 1 1 - (g : M2) 0 0 := by
    rw [Matrix.sub_apply, hadj]; simp
  rw [frobSq, e00, e01, e10, e11, h11, h10]
  simp only [normSq_re_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  have hns' : ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2
      + (((g : M2) 0 1).re ^ 2 + ((g : M2) 0 1).im ^ 2) = 1 := by
    rw [← normSq_re_im, ← normSq_re_im]; exact hns
  have hpyth := Real.sin_sq_add_cos_sq (su2Angle g)
  have hcos : Real.cos (su2Angle g) = ((g : M2) 0 0).re := by rw [hc, ht]; ring
  have hsin2 : Real.sin (su2Angle g) ^ 2 = 1 - ((g : M2) 0 0).re ^ 2 := by
    rw [← hcos]; linarith [hpyth]
  rw [hsin2]
  linarith [hns']

/-! ## §3 — `‖log g‖_F = √2·θ(g)` away from the junk point, `≤` everywhere

`SuTwoLogExpCore.su2Log` is `(κ/2)•(g − gᴴ)` with `κ = θ/sin θ`, and Lean's `0/0 = 0` makes it
return `0` at `g = ±1`. At `g = 1` that is the true logarithm; at `g = −1` it is a junk value
(the tree discloses this: `su2Log_center`, and `exp_log_fails_at_center`). Both statements below
are correct AT the junk point too — `≤` because the left side collapses to `0`. -/

theorem frobSq_su2Log_eq (g : SU2) (h1 : g ≠ 1) (h2 : g ≠ su2NegOne) :
    frobSq (su2Log g) = 2 * su2Angle g ^ 2 := by
  have hsin : Real.sin (su2Angle g) ≠ 0 := sin_su2Angle_ne_zero g h1 h2
  have hk : su2Kappa g = su2Angle g / Real.sin (su2Angle g) := rfl
  have hsmul : su2Log g = ((su2Kappa g / 2 : ℝ) : ℂ) • ((g : M2) - (g : M2)ᴴ) := by
    rw [su2Log]; norm_cast
  have hfs : frobSq (((su2Kappa g / 2 : ℝ) : ℂ) • ((g : M2) - (g : M2)ᴴ))
      = (su2Kappa g / 2) ^ 2 * frobSq ((g : M2) - (g : M2)ᴴ) := by
    have hn := frobNorm_real_smul (su2Kappa g / 2) ((g : M2) - (g : M2)ᴴ)
    have h1' := frobNorm_sq (((su2Kappa g / 2 : ℝ) : ℂ) • ((g : M2) - (g : M2)ᴴ))
    have h2' := frobNorm_sq ((g : M2) - (g : M2)ᴴ)
    rw [← h1', hn, mul_pow, sq_abs, h2']
  rw [hsmul, hfs, frobSq_sub_conjTranspose, hk]
  field_simp
  ring

theorem frobNorm_su2Log_eq (g : SU2) (h2 : g ≠ su2NegOne) :
    frobNorm (su2Log g) = Real.sqrt 2 * su2Angle g := by
  by_cases h1 : g = 1
  · subst h1
    have hang : su2Angle (1 : SU2) = 0 := by
      rw [su2Angle, coe_one, Matrix.trace_one]
      norm_num
    rw [su2Log_one, hang, frobNorm, frobSq]
    simp
  · have hfs := frobSq_su2Log_eq g h1 h2
    have hang := (su2Angle_mem g).1
    have h2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 2 * su2Angle g := by
      have := Real.sqrt_nonneg 2; positivity
    rw [frobNorm, hfs]
    have : (2 : ℝ) * su2Angle g ^ 2 = (Real.sqrt 2 * su2Angle g) ^ 2 := by
      rw [mul_pow, h2']
    rw [this, Real.sqrt_sq hnn]

theorem frobNorm_su2Log_le (g : SU2) : frobNorm (su2Log g) ≤ Real.sqrt 2 * su2Angle g := by
  by_cases h2 : g = su2NegOne
  · subst h2
    rw [su2Log_center, frobNorm, frobSq]
    have := (su2Angle_mem su2NegOne).1
    have := Real.sqrt_nonneg 2
    simp
    positivity
  · exact le_of_eq (frobNorm_su2Log_eq g h2)

/-! ## §4 — CMP98 (24) and (25), RE-DERIVED

> `|U − 1| = max_j |sin(λ_j/2)/(λ_j/2)| |λ_j| ≤ max_j |λ_j| = |log U|`   (24)
> `|log U| ≤ (π/2)|U − 1|, because |sin x / x| ≥ 2/π for x ∈ [−π/2, π/2]` (25)

(CMP98 printed p.21.) The source states them in the operator norm `|·|`; here they are proved in
`frobNorm`, in which BOTH sides of each are computed exactly from `θ`, so the constants are the
same: `‖g−1‖_F = 2√2 sin(θ/2)`, `‖log g‖_F = √2 θ`. Jordan's inequality is the only analytic
input, and Mathlib's `Real.mul_le_sin` is exactly the source's stated reason. -/

/-- **CMP98 (25), re-derived.** `‖log g‖_F ≤ (π/2)‖g − 1‖_F`, for EVERY `g ∈ SU(2)`.
No smallness hypothesis: the principal branch `arg ∈ ]−π,π]` of (23) makes `log` total, and the
constant `π/2` is attained in the limit `g → −1`. -/
theorem frobNorm_su2Log_le_pi_div_two (g : SU2) :
    frobNorm (su2Log g) ≤ (Real.pi / 2) * frobNorm ((g : M2) - 1) := by
  obtain ⟨hlo, hhi⟩ := su2Angle_mem g
  have hpi := Real.pi_pos
  -- Jordan: `2/π · (θ/2) ≤ sin (θ/2)`
  have hj : 2 / Real.pi * (su2Angle g / 2) ≤ Real.sin (su2Angle g / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hkey : su2Angle g ≤ Real.pi * Real.sin (su2Angle g / 2) := by
    have := mul_le_mul_of_nonneg_left hj (le_of_lt hpi)
    have hcalc : Real.pi * (2 / Real.pi * (su2Angle g / 2)) = su2Angle g := by
      field_simp
    linarith [hcalc ▸ this]
  have hs2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  calc frobNorm (su2Log g) ≤ Real.sqrt 2 * su2Angle g := frobNorm_su2Log_le g
    _ ≤ Real.sqrt 2 * (Real.pi * Real.sin (su2Angle g / 2)) := by nlinarith
    _ = (Real.pi / 2) * (2 * Real.sqrt 2 * Real.sin (su2Angle g / 2)) := by ring
    _ = (Real.pi / 2) * frobNorm ((g : M2) - 1) := by rw [frobNorm_sub_one_eq]

/-- **CMP98 (24), re-derived** (principal-branch form). `‖g − 1‖_F ≤ ‖log g‖_F`.
The hypothesis `g ≠ su2NegOne` is exactly the junk point of `SuTwoLogExpCore.su2Log`; §5 shows it
is discharged by the branch condition `su2Exp H = g ∧ su2Log g = H`. -/
theorem frobNorm_sub_one_le_frobNorm_su2Log (g : SU2) (h2 : g ≠ su2NegOne) :
    frobNorm ((g : M2) - 1) ≤ frobNorm (su2Log g) := by
  have hs := Real.sin_le (by linarith [(su2Angle_mem g).1] : (0:ℝ) ≤ su2Angle g / 2)
  have hs2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  rw [frobNorm_sub_one_eq, frobNorm_su2Log_eq g h2]
  nlinarith

/-! ## §5 — THE BLOCKING STEP (43), AND THE ESTIMATE

`blockedLink` is (43) transcribed. The `i` and `1/i` cancel: `exp[i Σ w (1/i) log X] = exp[Σ w log X]`.
The averaging index set is `B(c₋)`, the weights are `w x = L^{−d}` (`hsum : Σ w = 1`, since
`|B(c₋)| = L^d`), `W x = U(Γ_{c,x})·U(c)^{−1}`, and `Uc = U(c)`. -/

/-- The Lie-algebra element in the exponent of (43): `H = Σ_{x∈B(c₋)} L^{−d}·log W_x`. -/
noncomputable def blockExponent {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ι → SU2) : M2 :=
  ∑ x ∈ s, ((w x : ℝ) : ℂ) • su2Log (W x)

/-- **CMP98 (43).** -/
noncomputable def blockedLink {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ι → SU2) (Uc : SU2) :
    SU2 :=
  su2Exp (blockExponent s w W) * Uc

/-- **S3, the averaging bound.** `‖H‖_F ≤ c` whenever every `‖log W_x‖_F ≤ c` and the weights are
nonnegative with `Σ w = 1`. The `L^{−d}` normalisation is used ONLY through `Σ w = 1`; the count
`|B(c₋)| = L^d` is what makes that true, and no other property of the block is needed. -/
theorem frobNorm_blockExponent_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ι → SU2)
    (c : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1)
    (hbd : ∀ x ∈ s, frobNorm (su2Log (W x)) ≤ c) :
    frobNorm (blockExponent s w W) ≤ c := by
  have hstep : ∀ x ∈ s, frobNorm (((w x : ℝ) : ℂ) • su2Log (W x)) ≤ w x * c := by
    intro x hx
    rw [frobNorm_real_smul, abs_of_nonneg (hw x hx)]
    exact mul_le_mul_of_nonneg_left (hbd x hx) (hw x hx)
  calc frobNorm (blockExponent s w W)
      ≤ ∑ x ∈ s, frobNorm (((w x : ℝ) : ℂ) • su2Log (W x)) := frobNorm_sum_le s _
    _ ≤ ∑ x ∈ s, w x * c := Finset.sum_le_sum hstep
    _ = (∑ x ∈ s, w x) * c := by rw [Finset.sum_mul]
    _ = c := by rw [hsum, one_mul]

/-- **S3', the exponential bound**, in the form that carries the branch condition explicitly.
`hbranch` is `su2Log (su2Exp H) = H`: exactly Balaban's (23) principal branch. It rules out the ONE
junk point of `su2Log`, and there it is genuinely needed — `su2Exp 0 = 1 ≠ −1 = su2NegOne`. -/
theorem frobNorm_su2Exp_sub_one_le (H : M2) (hbranch : su2Log (su2Exp H) = H) :
    frobNorm ((su2Exp H : M2) - 1) ≤ frobNorm H := by
  by_cases hneg : su2Exp H = su2NegOne
  · exfalso
    have h0 : H = 0 := by rw [← hbranch, hneg, su2Log_center]
    rw [h0] at hneg
    rw [su2Exp_zero] at hneg
    exact su2NegOne_ne_one hneg.symm
  · have := frobNorm_sub_one_le_frobNorm_su2Log (su2Exp H) hneg
    rwa [hbranch] at this

/-- **THE BLOCKING LINK ESTIMATE — (43) turned into the recursion.**

`‖Ū_c − 1‖ ≤ Lreal·eps + (π/2)·Nplaq·beta`.

* `hUc` is S2: `Uc = U(c)` spans `L` fine bonds, so `‖U(c) − 1‖ ≤ L·ε` by telescoping. The
  coefficient of `eps` is therefore **exactly `Lreal`**, with nothing hidden in it.
* `hloop` is S5: each `W x = U(Γ_{c,x})U(c)^{−1}` is a CLOSED-LOOP holonomy, hence bounded by
  (number of plaquettes of a spanning surface) × (curvature). §6 supplies `Nplaq = N(d,L)` from
  the p.19 definition of `Γ_{c,x}`.
* `hbranch` is the principal branch of (23).

Nothing else is assumed. In particular there is **no smallness hypothesis**: `frobNorm_su2Log_le_pi_div_two`
is unconditional. -/
theorem blockedLink_sub_one_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ι → SU2) (Uc : SU2)
    (Lreal eps Nplaq beta : ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1)
    (hUc : frobNorm ((Uc : M2) - 1) ≤ Lreal * eps)
    (hloop : ∀ x ∈ s, frobNorm ((W x : M2) - 1) ≤ Nplaq * beta)
    (hbranch : su2Log (su2Exp (blockExponent s w W)) = blockExponent s w W) :
    frobNorm ((blockedLink s w W Uc : M2) - 1)
      ≤ Lreal * eps + (Real.pi / 2 * Nplaq) * beta := by
  have hlog : ∀ x ∈ s, frobNorm (su2Log (W x)) ≤ (Real.pi / 2) * (Nplaq * beta) := by
    intro x hx
    refine le_trans (frobNorm_su2Log_le_pi_div_two (W x)) ?_
    exact mul_le_mul_of_nonneg_left (hloop x hx) (by positivity)
  have hH : frobNorm (blockExponent s w W) ≤ (Real.pi / 2) * (Nplaq * beta) :=
    frobNorm_blockExponent_le s w W _ hw hsum hlog
  have hE : frobNorm ((su2Exp (blockExponent s w W) : M2) - 1) ≤ (Real.pi / 2) * (Nplaq * beta) :=
    le_trans (frobNorm_su2Exp_sub_one_le _ hbranch) hH
  calc frobNorm ((blockedLink s w W Uc : M2) - 1)
      ≤ frobNorm ((su2Exp (blockExponent s w W) : M2) - 1) + frobNorm ((Uc : M2) - 1) :=
        AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _
    _ ≤ (Real.pi / 2) * (Nplaq * beta) + Lreal * eps := add_le_add hE hUc
    _ = Lreal * eps + (Real.pi / 2 * Nplaq) * beta := by ring

/-! ## §6 — THE CONSTANT `N(d,L)`, COUNTED FROM THE p.19 DEFINITION OF `Γ_{c,x}`

CMP98 p.19, prose under (14) — the DEFINITION, which is NOT on p.24:

> "Let us notice that `Γ_{c₋,x} ∪ [x, x(c)] ∪ Γ_{x(c),c₊}` is an oriented contour with `c₋` as an
> initial point and `c₊` as a final point. We denote it by `Γ_{c,x}`."

So `W_x = U(Γ_{c,x})·U(c)^{−1}` is the holonomy of the CLOSED loop `Γ_{c,x} ∪ (−c)`, and it is
bounded by (plaquettes of a spanning surface) × (curvature). The surface splits in two, and both
pieces are counted here exactly.

* **Cylinder.** `Γ_{x(c),c₊}` is the translate of `Γ_{x,c₋}` by the coarse bond. Translating
  `Γ_{c₋,x}` through `c` sweeps a tube: `L` plaquettes per staircase bond, except that a bond in
  direction `μ` (the direction of `c`) sweeps a degenerate tube and contributes `0`.
  Count `= L·Σ_{ρ≠μ} x_ρ`.
* **Reversal.** What is left is the loop between the two EXTREME monotone staircases from `c₋` to
  `x`: the forward one (coordinate order `d,…,1`, per p.24) and the reverse of the backward one
  (order `1,…,d`). Reversing a `d`-block word by adjacent transpositions swaps each unordered pair
  `{ρ,ν}` exactly once, and swapping blocks of lengths `x_ρ, x_ν` sweeps an `x_ρ·x_ν` rectangle.
  Count `= Σ_{ρ<ν} x_ρ x_ν`.

Maximised over `x ∈ B(c₋) = {0,…,L−1}^d` — both are maximal at `x = (L−1,…,L−1)` — this gives

  `N(d,L) = (d−1)·L·(L−1) + C(d,2)·(L−1)²`,   `plaqCount` below.
-/

/-- **The one-bond lasso count.** For a bond in direction `ν` at offset `x` from the axial base
point, the tube over the staircase suffix in the directions strictly BELOW `ν`. -/
def lassoCount {d : ℕ} (x : Fin d → ℕ) (ν : Fin d) : ℕ := ∑ ρ ∈ Finset.Iio ν, x ρ

/-- **CMP98 p.24, printed, as a theorem** (image-verified, `compute/kuniform_cr/renders/CMP98_pdf8-08.png`):

> "The conditions `V₀(Γ_{y,x}) = 1` imply `V₀(x,x+e₁) = 1`, `|V₀(x,x+e₂)−1| < |x₁−y₁|α₀`,
> `|V₀(x,x+e₃)−1| < (|x₁−y₁|+|x₂−y₂|)α₀`, …, `|V₀(x,x+e_μ)−1| < (|x₁−y₁|+…+|x_{μ−1}−y_{μ−1}|)α₀`"

Direction `1` (Lean index `0`) carries `0` plaquettes — the printed EXACT equality `V₀(x,x+e₁)=1`.
This is the source printing this module's counting rule for the one-bond case, and it is what pins
the staircase coordinate order (direction `1` changed LAST). -/
theorem lassoCount_dir_one {d : ℕ} (x : Fin d → ℕ) (h : 0 < d) :
    lassoCount x ⟨0, h⟩ = 0 := by
  have hempty : Finset.Iio (⟨0, h⟩ : Fin d) = ∅ := by
    ext a
    simp [Fin.lt_def]
  rw [lassoCount, hempty, Finset.sum_empty]

/-- Printed p.24: `|V₀(x,x+e₂)−1| < |x₁−y₁|α₀` — one plaquette-row, weight `x₁`. -/
theorem lassoCount_dir_two (x : Fin 3 → ℕ) : lassoCount x 1 = x 0 := by
  have h : Finset.Iio (1 : Fin 3) = {0} := by decide
  rw [lassoCount, h, Finset.sum_singleton]

/-- Printed p.24: `|V₀(x,x+e₃)−1| < (|x₁−y₁|+|x₂−y₂|)α₀`. -/
theorem lassoCount_dir_three (x : Fin 3 → ℕ) : lassoCount x 2 = x 0 + x 1 := by
  have h : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  rw [lassoCount, h]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Cylinder plaquette count: `L·Σ_{ρ≠μ} x_ρ`. -/
def cylCount {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (μ : Fin d) : ℕ :=
  ell * ∑ ρ ∈ Finset.univ.erase μ, x ρ

/-- Reversal plaquette count: `Σ_{ρ<ν} x_ρ x_ν`. -/
def revCount {d : ℕ} (x : Fin d → ℕ) : ℕ := ∑ ν, ∑ ρ ∈ Finset.Iio ν, x ρ * x ν

/-- The plaquette count of the explicit spanning surface of `Γ_{c,x} ∪ (−c)`. -/
def surfCount {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (μ : Fin d) : ℕ := cylCount ell x μ + revCount x

/-- **`N(d,L)`.** -/
def plaqCount (d ell : ℕ) : ℕ := (d - 1) * ell * (ell - 1) + (d.choose 2) * (ell - 1) ^ 2

/-- **`Kb(d,L) = (π/2)·N(d,L)`.** Note the signature: `d` and `ell` ONLY. There is no level
argument, and none can be added — every ingredient of the derivation is either the block geometry,
identical at every RG step because (43) applies the one-step operation (42) to the field on
`Ω^{(k)}`, or a universal `SU(2)` constant. -/
noncomputable def KbConst (d ell : ℕ) : ℝ := (Real.pi / 2) * (plaqCount d ell : ℝ)

theorem sum_fin_val (d : ℕ) : ∑ ν : Fin d, (ν : ℕ) = d.choose 2 := by
  have h1 : ∑ ν : Fin d, (ν : ℕ) = ∑ i ∈ Finset.range d, i :=
    Fin.sum_univ_eq_sum_range (fun i => i) d
  have h2 := Finset.sum_range_id_mul_two d
  have h3 := Nat.choose_two_right d
  omega

theorem cylCount_le {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (μ : Fin d) (hx : ∀ ρ, x ρ ≤ ell - 1) :
    cylCount ell x μ ≤ (d - 1) * ell * (ell - 1) := by
  classical
  have hcard : (Finset.univ.erase μ).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ μ), Finset.card_univ, Fintype.card_fin]
  have h := Finset.sum_le_card_nsmul (Finset.univ.erase μ) x (ell - 1) (fun r _ => hx r)
  rw [hcard, smul_eq_mul] at h
  calc cylCount ell x μ ≤ ell * ((d - 1) * (ell - 1)) := Nat.mul_le_mul_left _ h
    _ = (d - 1) * ell * (ell - 1) := by ring

theorem revCount_le {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (hx : ∀ ρ, x ρ ≤ ell - 1) :
    revCount x ≤ (d.choose 2) * (ell - 1) ^ 2 := by
  classical
  have hinner : ∀ ν : Fin d, ∑ ρ ∈ Finset.Iio ν, x ρ * x ν ≤ (ν : ℕ) * (ell - 1) ^ 2 := by
    intro ν
    have hterm : ∀ ρ ∈ Finset.Iio ν, x ρ * x ν ≤ (ell - 1) ^ 2 := by
      intro ρ _
      have := hx ρ; have := hx ν
      calc x ρ * x ν ≤ (ell - 1) * (ell - 1) := Nat.mul_le_mul (hx ρ) (hx ν)
        _ = (ell - 1) ^ 2 := by ring
    have h := Finset.sum_le_card_nsmul (Finset.Iio ν) (fun ρ => x ρ * x ν) ((ell - 1) ^ 2) hterm
    rwa [Fin.card_Iio, smul_eq_mul] at h
  calc revCount x ≤ ∑ ν : Fin d, (ν : ℕ) * (ell - 1) ^ 2 := Finset.sum_le_sum (fun ν _ => hinner ν)
    _ = (∑ ν : Fin d, (ν : ℕ)) * (ell - 1) ^ 2 := by rw [Finset.sum_mul]
    _ = (d.choose 2) * (ell - 1) ^ 2 := by rw [sum_fin_val]

/-- **THE COUNT.** Every `x` in the block `B(c₋) = {0,…,L−1}^d` gives a spanning surface with at
most `N(d,L)` plaquettes, and the bound is attained at `x = (L−1,…,L−1)`. -/
theorem surfCount_le {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (μ : Fin d) (hx : ∀ ρ, x ρ ≤ ell - 1) :
    surfCount ell x μ ≤ plaqCount d ell :=
  Nat.add_le_add (cylCount_le ell x μ hx) (revCount_le ell x hx)

/-- The count is ATTAINED, so `N(d,L)` is not slack that could be shrunk by a better `x`:
at `x ≡ L−1` the cylinder piece alone already equals `(d−1)L(L−1)`. -/
theorem cylCount_eq_at_max {d : ℕ} (ell : ℕ) (μ : Fin d) :
    cylCount ell (fun _ => ell - 1) μ = (d - 1) * ell * (ell - 1) := by
  classical
  have hcard : (Finset.univ.erase μ).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ μ), Finset.card_univ, Fintype.card_fin]
  rw [cylCount, Finset.sum_const, hcard, smul_eq_mul]
  ring

/-! ### §6b — the values, and the cross-checks against print -/

theorem plaqCount_3_2 : plaqCount 3 2 = 7 := by decide +kernel
theorem plaqCount_3_3 : plaqCount 3 3 = 24 := by decide +kernel
theorem plaqCount_4_2 : plaqCount 4 2 = 12 := by decide +kernel
theorem plaqCount_3_4 : plaqCount 3 4 = 51 := by decide +kernel

/-- **`GammaLevelDefect`'s ASSUMED `Kb = 12` at `d=3, ell=2` is conservative — the COUNTED value is
`7π/2 ≈ 10.996 < 12`.** So every consumer of `hlink` instantiated at `Kb = 12` survives the
replacement of the assumption by this derivation; the derivation does not weaken anything already
banked. (`GammaLevelDefect`'s `Ecst` is increasing in `Kb`, so a smaller `Kb` only lowers the bar.) -/
theorem KbConst_3_2_lt_twelve : KbConst 3 2 < 12 := by
  rw [KbConst, plaqCount_3_2]
  have hp : Real.pi < 3.15 := Real.pi_lt_d2
  push_cast
  linarith

theorem KbConst_3_2_pos : 0 < KbConst 3 2 := by
  rw [KbConst, plaqCount_3_2]
  have hp := Real.pi_pos
  push_cast
  linarith

/-- **Cross-check against CMP98 p.25, image-verified: `|Γ_{c,x}| < (2d+1)L`.**
Counted independently from the p.19 definition `Γ_{c,x} = Γ_{c₋,x} ∪ [x,x(c)] ∪ Γ_{x(c),c₊}`:
`Σ_ρ x_ρ + L + Σ_ρ x_ρ ≤ 2d(L−1) + L = (2d+1)L − 2d`. The two counts agree, and ours is strictly
sharper by `2d` — which is why the source can write `<`. -/
def gammaPathLength {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) : ℕ := (∑ ρ, x ρ) + ell + (∑ ρ, x ρ)

theorem gammaPathLength_le {d : ℕ} (n : ℕ) (x : Fin d → ℕ) (hx : ∀ ρ, x ρ ≤ n) :
    gammaPathLength (n + 1) x + 2 * d ≤ (2 * d + 1) * (n + 1) := by
  classical
  have hsum : ∑ ρ, x ρ ≤ d * n := by
    have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin d)) x n (fun r _ => hx r)
    rwa [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have hexp : (2 * d + 1) * (n + 1) = 2 * (d * n) + (2 * d + n + 1) := by ring
  rw [gammaPathLength, hexp]
  omega

/-! ## §7 — `hlink` PRODUCED, WITH ONE `Kb` FOR ALL LEVELS

This is the shape `GammaLevelDefect.hlink` assumes, now derived from (43). Read the type: `KbConst`
takes `d` and `ell` and NOTHING ELSE, while the hypotheses and the conclusion range over every
level `l < k`. That is the `k`-uniformity, made visible in the signature rather than argued in
prose. -/

/-- **THE LINK RECURSION.**

    `eps (l+1) ≤ ell · eps l + KbConst d ell · beta l`,  for every `l < k`, with ONE `KbConst d ell`.

Every hypothesis is an instance of (43)'s own data at level `l`:

* `s l` is the block `B(c₋)`, `w l` the weights `L^{−d}` (only `Σ w = 1` is used, which is exactly
  `|B(c₋)| = L^d`), `W l x = Ū^l(Γ_{c,x})·Ū^l(c)^{−1}`, `Uc l = Ū^l(c)`;
* `hUc` is the telescoping `‖Ū^l(c) − 1‖ ≤ L·ε_l` over the `L` fine bonds of `c`;
* `hloop` is the closed-loop bound with the COUNTED `plaqCount d ell` of §6;
* `hbranch` is Balaban's (23) principal branch (§8 discharges it from a curvature smallness);
* `hnext` says `ε_{l+1}` is a bound for the blocked link, i.e. it is the level-`(l+1)` link defect.

No smallness hypothesis appears. -/
theorem link_recursion_of_blocking
    (d ell k : ℕ) (eps beta : ℕ → ℝ)
    {ι : Type*} (s : ℕ → Finset ι) (w : ℕ → ι → ℝ) (W : ℕ → ι → SU2) (Uc : ℕ → SU2)
    (hw : ∀ l, ∀ x ∈ s l, 0 ≤ w l x)
    (hsum : ∀ l, ∑ x ∈ s l, w l x = 1)
    (hUc : ∀ l, l < k → frobNorm ((Uc l : M2) - 1) ≤ (ell : ℝ) * eps l)
    (hloop : ∀ l, l < k → ∀ x ∈ s l,
        frobNorm ((W l x : M2) - 1) ≤ (plaqCount d ell : ℝ) * beta l)
    (hbranch : ∀ l, l < k →
        su2Log (su2Exp (blockExponent (s l) (w l) (W l))) = blockExponent (s l) (w l) (W l))
    (hnext : ∀ l, l < k →
        eps (l + 1) ≤ frobNorm ((blockedLink (s l) (w l) (W l) (Uc l) : M2) - 1)) :
    ∀ l, l < k → eps (l + 1) ≤ (ell : ℝ) * eps l + KbConst d ell * beta l := by
  intro l hl
  refine le_trans (hnext l hl) ?_
  have h := blockedLink_sub_one_le (s l) (w l) (W l) (Uc l) (ell : ℝ) (eps l)
    (plaqCount d ell : ℝ) (beta l) (hw l) (hsum l) (hUc l hl) (hloop l hl) (hbranch l hl)
  rw [KbConst]
  exact h

/-! ## §8 — `hbranch` IS NOT AN EXTRA ASSUMPTION: it follows from the curvature bound

The dispatch question: *"the log/exp step needs the argument to be in the domain where `log` is
well defined — state that hypothesis explicitly and check it is implied by the curvature bound
already assumed, not an extra one smuggled in."*

Answer: it is implied. `H = Σ w_x log W_x` is an `su(2)` element with `‖H‖_F = √2·r`, `r` its
angle; `su2Log (su2Exp H) = H` holds as soon as `r < π`, i.e. `‖H‖_F < √2·π`; and §5 already
proves `‖H‖_F ≤ (π/2)·N·β`. So

    N(d,L)·β < 2√2   ⟹   hbranch.

`2√2` is the maximal `‖g − 1‖_F` on `SU(2)`, attained only at `g = −1`: the condition says exactly
"the loop holonomies `W_x` do not reach the antipode", which is the honest content of Balaban's
`log` being on its principal branch. It is a bound on the INPUT curvature, not on the output.

The route is an explicit diagonalisation `H = g·psiR r·gᴴ`, written out with its `SU(2)`
diagonaliser in closed form — no existential over free data, no appeal to a spectral theorem. -/

/-- The `su(2)` carrier: anti-hermitian and traceless. -/
def IsSuTwoAlg (H : M2) : Prop := Hᴴ = -H ∧ Matrix.trace H = 0

theorem isSuTwoAlg_su2Log (g : SU2) : IsSuTwoAlg (su2Log g) := by
  constructor
  · have hstar : star (((su2Kappa g : ℝ) : ℂ) / 2) = ((su2Kappa g : ℝ) : ℂ) / 2 := by
      simp [Complex.conj_ofReal]
    rw [su2Log, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, hstar,
      show ((g : M2)ᴴ - (g : M2)) = -((g : M2) - (g : M2)ᴴ) by abel, smul_neg]
  · exact su2Log_traceless g

theorem isSuTwoAlg_zero : IsSuTwoAlg (0 : M2) := by
  constructor <;> simp

theorem isSuTwoAlg_add {A B : M2} (hA : IsSuTwoAlg A) (hB : IsSuTwoAlg B) : IsSuTwoAlg (A + B) := by
  constructor
  · rw [Matrix.conjTranspose_add, hA.1, hB.1, neg_add]
  · rw [Matrix.trace_add, hA.2, hB.2, add_zero]

theorem isSuTwoAlg_real_smul (c : ℝ) {A : M2} (hA : IsSuTwoAlg A) : IsSuTwoAlg ((c : ℂ) • A) := by
  constructor
  · have hstar : star ((c : ℂ)) = ((c : ℂ)) := by simp [Complex.conj_ofReal]
    rw [Matrix.conjTranspose_smul, hA.1, hstar, smul_neg]
  · rw [Matrix.trace_smul, hA.2, smul_zero]

theorem isSuTwoAlg_blockExponent {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ι → SU2) :
    IsSuTwoAlg (blockExponent s w W) := by
  classical
  rw [blockExponent]
  induction s using Finset.induction_on with
  | empty => simpa using isSuTwoAlg_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSuTwoAlg_add (isSuTwoAlg_real_smul _ (isSuTwoAlg_su2Log _)) ih

/-! ### §8a — the entry form of an `su(2)` element -/

theorem suTwoAlg_e11 {H : M2} (h : IsSuTwoAlg H) : H 1 1 = -H 0 0 := by
  have := h.2
  rw [Matrix.trace_fin_two] at this
  linear_combination this

theorem suTwoAlg_e00_re {H : M2} (h : IsSuTwoAlg H) : (H 0 0).re = 0 := by
  have hc := congrFun (congrFun h.1 0) 0
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def] at hc
  have := congrArg Complex.re hc
  simp only [Complex.conj_re, Complex.neg_re] at this
  linarith

theorem suTwoAlg_e10 {H : M2} (h : IsSuTwoAlg H) : H 1 0 = -(star (H 0 1)) := by
  have hc := congrFun (congrFun h.1 0) 1
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at hc
  have h2 := congrArg star hc
  rwa [star_star, star_neg] at h2

/-- `H² = −(z² + |w|²)·1` for `H ∈ su(2)`, `z = Im H₀₀`, `w = H₀₁`.
Cayley–Hamilton in `2×2`, by direct entry computation — no spectral theorem. -/
theorem suTwoAlg_sq {H : M2} (h : IsSuTwoAlg H) :
    frobSq H = 2 * ((H 0 0).im ^ 2 + Complex.normSq (H 0 1)) := by
  have h11 := suTwoAlg_e11 h
  have h10 := suTwoAlg_e10 h
  have h00 := suTwoAlg_e00_re h
  rw [frobSq, h11, h10]
  simp only [normSq_re_im, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  rw [h00]
  ring

/-- The angle of an `su(2)` element: `r = √(z² + |w|²) = ‖H‖_F/√2`. -/
noncomputable def algAngle (H : M2) : ℝ :=
  Real.sqrt ((H 0 0).im ^ 2 + Complex.normSq (H 0 1))

theorem algAngle_nonneg (H : M2) : 0 ≤ algAngle H := Real.sqrt_nonneg _

theorem algAngle_sq (H : M2) : algAngle H ^ 2 = (H 0 0).im ^ 2 + Complex.normSq (H 0 1) :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))

/-- `‖H‖_F = √2·r`. -/
theorem frobNorm_eq_sqrt_two_mul_algAngle {H : M2} (h : IsSuTwoAlg H) :
    frobNorm H = Real.sqrt 2 * algAngle H := by
  have hsq := suTwoAlg_sq h
  have hr := algAngle_sq H
  have hrnn := algAngle_nonneg H
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 * algAngle H := by have := Real.sqrt_nonneg 2; positivity
  rw [frobNorm, hsq, ← hr]
  have : (2 : ℝ) * algAngle H ^ 2 = (Real.sqrt 2 * algAngle H) ^ 2 := by rw [mul_pow, h2]
  rw [this, Real.sqrt_sq hnn]

/-! ### §8b — the explicit `SU(2)` diagonaliser -/

/-- The standard `SU(2)` parametrisation `[[a, −b̄],[b, ā]]`. -/
def su2Of (a b : ℂ) : M2 := !![a, -(star b); b, star a]

@[simp] theorem su2Of_00 (a b : ℂ) : su2Of a b 0 0 = a := by simp [su2Of]
@[simp] theorem su2Of_01 (a b : ℂ) : su2Of a b 0 1 = -(star b) := by simp [su2Of]
@[simp] theorem su2Of_10 (a b : ℂ) : su2Of a b 1 0 = b := by simp [su2Of]
@[simp] theorem su2Of_11 (a b : ℂ) : su2Of a b 1 1 = star a := by simp [su2Of]

theorem su2Of_mem (a b : ℂ) (h : a * star a + b * star b = 1) :
    su2Of a b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have h' : a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1 := by
    simpa [Complex.star_def] using h
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Complex.star_def] <;>
      ring_nf <;>
      first
        | linear_combination h'
        | linear_combination -h'
  · rw [Matrix.det_fin_two]
    simp only [su2Of_00, su2Of_01, su2Of_10, su2Of_11]
    linear_combination h

/-- **The conjugation formula.** `g·psiR r·gᴴ` in closed form for `g = su2Of a b`. -/
theorem su2Of_conj_psiR (a b : ℂ) (r : ℝ) :
    su2Of a b * psiR r * (su2Of a b)ᴴ
      = !![(r : ℂ) * Complex.I * (a * star a - b * star b),
             2 * (r : ℂ) * Complex.I * (a * star b);
           2 * (r : ℂ) * Complex.I * (star a * b),
             -((r : ℂ) * Complex.I * (a * star a - b * star b))] := by
  have hp := psiR_dg r
  have p00 : psiR r 0 0 = (r : ℂ) * Complex.I := by rw [hp, dg_00]
  have p11 : psiR r 1 1 = -((r : ℂ) * Complex.I) := by rw [hp, dg_11]
  have p01 : psiR r 0 1 = 0 := by rw [hp, dg_01]
  have p10 : psiR r 1 0 = 0 := by rw [hp, dg_10]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      p00, p11, p01, p10, Complex.star_def] <;> ring

/-! ### §8c — the diagonaliser in closed form, and the branch discharge -/

/-- The `SU(2)` diagonaliser of an `su(2)` element, in closed form. It is a FUNCTION of `H` —
there is no existential over free data, so no `S91` row is needed and no prover can pick an easy
instance. Three cases: `w = 0` (already diagonal, up to the Weyl flip when `z < 0`) and `w ≠ 0`. -/
noncomputable def diagPair (H : M2) : ℂ × ℂ :=
  if H 0 1 = 0 then (if 0 ≤ (H 0 0).im then (1, 0) else (0, 1))
  else
    ((H 0 1) / ((Real.sqrt (2 * algAngle H * (algAngle H - (H 0 0).im)) : ℝ) : ℂ),
      Complex.I * ((algAngle H - (H 0 0).im : ℝ) : ℂ)
        / ((Real.sqrt (2 * algAngle H * (algAngle H - (H 0 0).im)) : ℝ) : ℂ))

theorem algAngle_pos_of_ne {H : M2} (hw : H 0 1 ≠ 0) : 0 < algAngle H := by
  have hns : 0 < Complex.normSq (H 0 1) := Complex.normSq_pos.mpr hw
  have : 0 < (H 0 0).im ^ 2 + Complex.normSq (H 0 1) := by positivity
  exact Real.sqrt_pos.mpr this

theorem algAngle_gt_im_of_ne {H : M2} (hw : H 0 1 ≠ 0) : (H 0 0).im < algAngle H := by
  have hr := algAngle_sq H
  have hrpos := algAngle_pos_of_ne hw
  have hns : 0 < Complex.normSq (H 0 1) := Complex.normSq_pos.mpr hw
  nlinarith [hr, hrpos, hns, sq_nonneg ((H 0 0).im - algAngle H)]

/-- `N² = 2r(r−z)`, and `N > 0` when `w ≠ 0`. -/
theorem diagNorm_sq {H : M2} (hw : H 0 1 ≠ 0) :
    (Real.sqrt (2 * algAngle H * (algAngle H - (H 0 0).im))) ^ 2
      = 2 * algAngle H * (algAngle H - (H 0 0).im) := by
  have h1 := algAngle_pos_of_ne hw
  have h2 := algAngle_gt_im_of_ne hw
  exact Real.sq_sqrt (by nlinarith)

theorem diagNorm_pos {H : M2} (hw : H 0 1 ≠ 0) :
    0 < Real.sqrt (2 * algAngle H * (algAngle H - (H 0 0).im)) := by
  have h1 := algAngle_pos_of_ne hw
  have h2 := algAngle_gt_im_of_ne hw
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem suTwoAlg_e00 {H : M2} (h : IsSuTwoAlg H) :
    H 0 0 = (((H 0 0).im : ℝ) : ℂ) * Complex.I := by
  have hre := suTwoAlg_e00_re h
  apply Complex.ext <;> simp [hre]

/-! The `w ≠ 0` branch, packaged as three scalar identities so that all the algebra happens in `ℝ`
and only the final cast is complex. -/

theorem diagPair_fst {H : M2} (hw : H 0 1 ≠ 0) :
    (diagPair H).1
      = H 0 1 / ((Real.sqrt (2 * algAngle H * (algAngle H - (H 0 0).im)) : ℝ) : ℂ) := by
  simp [diagPair, if_neg hw]

theorem diagPair_snd {H : M2} (hw : H 0 1 ≠ 0) :
    (diagPair H).2
      = Complex.I * ((algAngle H - (H 0 0).im : ℝ) : ℂ)
          / ((Real.sqrt (2 * algAngle H * (algAngle H - (H 0 0).im)) : ℝ) : ℂ) := by
  simp [diagPair, if_neg hw]

/-- `a·ā = (r+z)/(2r)`. -/
theorem diagPair_aa {H : M2} (h : IsSuTwoAlg H) (hw : H 0 1 ≠ 0) :
    (diagPair H).1 * star (diagPair H).1
      = (((algAngle H + (H 0 0).im) / (2 * algAngle H) : ℝ) : ℂ) := by
  have hrpos := algAngle_pos_of_ne hw
  have hgt := algAngle_gt_im_of_ne hw
  have hNsq := diagNorm_sq hw
  have hNpos := diagNorm_pos hw
  have hr := algAngle_sq H
  set r := algAngle H with hrdef
  set z := (H 0 0).im with hzdef
  set N := Real.sqrt (2 * r * (r - z)) with hNdef
  have hnormsq : Complex.normSq (H 0 1) = r ^ 2 - z ^ 2 := by linarith [hr]
  have h1 : r ≠ 0 := ne_of_gt hrpos
  have h2 : r - z ≠ 0 := by intro hc; apply h1; nlinarith [sub_eq_zero.mp hc]
  rw [diagPair_fst hw, ← hrdef, ← hzdef, ← hNdef]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  rw [div_mul_div_comm, Complex.mul_conj, hnormsq]
  have hNN : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) = (((N ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hNN, ← Complex.ofReal_div]
  congr 1
  rw [hNsq]
  field_simp
  ring

/-- `b·b̄ = (r−z)/(2r)`. -/
theorem diagPair_bb {H : M2} (hw : H 0 1 ≠ 0) :
    (diagPair H).2 * star (diagPair H).2
      = (((algAngle H - (H 0 0).im) / (2 * algAngle H) : ℝ) : ℂ) := by
  have hrpos := algAngle_pos_of_ne hw
  have hgt := algAngle_gt_im_of_ne hw
  have hNsq := diagNorm_sq hw
  have hNpos := diagNorm_pos hw
  set r := algAngle H with hrdef
  set z := (H 0 0).im with hzdef
  set N := Real.sqrt (2 * r * (r - z)) with hNdef
  have h1 : r ≠ 0 := ne_of_gt hrpos
  have h2 : r - z ≠ 0 := by intro hc; apply h1; nlinarith [sub_eq_zero.mp hc]
  rw [diagPair_snd hw, ← hrdef, ← hzdef, ← hNdef]
  simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  have hI := Complex.I_mul_I
  have hnum : Complex.I * ((r - z : ℝ) : ℂ) * (-Complex.I * ((r - z : ℝ) : ℂ))
      = ((((r - z) ^ 2 : ℝ)) : ℂ) := by
    push_cast
    linear_combination (-((((r : ℝ) : ℂ) - ((z : ℝ) : ℂ)) ^ 2)) * hI
  rw [hnum]
  have hNN : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) = (((N ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hNN, ← Complex.ofReal_div]
  congr 1
  rw [hNsq]
  field_simp

/-- `a·b̄ = −i·w/(2r)`. -/
theorem diagPair_ab {H : M2} (hw : H 0 1 ≠ 0) :
    (diagPair H).1 * star (diagPair H).2
      = -Complex.I * H 0 1 * (((1 / (2 * algAngle H)) : ℝ) : ℂ) := by
  have hrpos := algAngle_pos_of_ne hw
  have hgt := algAngle_gt_im_of_ne hw
  have hNsq := diagNorm_sq hw
  have hNpos := diagNorm_pos hw
  set r := algAngle H with hrdef
  set z := (H 0 0).im with hzdef
  set N := Real.sqrt (2 * r * (r - z)) with hNdef
  have h1 : r ≠ 0 := ne_of_gt hrpos
  have h2 : r - z ≠ 0 := by intro hc; apply h1; nlinarith [sub_eq_zero.mp hc]
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by simpa using h1
  have hrzC : ((r - z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2
  rw [diagPair_fst hw, diagPair_snd hw, ← hrdef, ← hzdef, ← hNdef]
  simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  have hNN : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) = (((2 * r * (r - z) : ℝ)) : ℂ) := by
    have hx : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) = (((N ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hx, hNsq]
  rw [hNN]
  have hden : (((2 * r * (r - z) : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro hc
    rcases mul_eq_zero.mp hc with hc1 | hc2
    · rcases mul_eq_zero.mp hc1 with hc3 | hc4
      · norm_num at hc3
      · exact h1 hc4
    · exact h2 hc2
  rw [div_eq_iff hden]
  push_cast
  field_simp

theorem diagPair_norm {H : M2} (h : IsSuTwoAlg H) :
    (diagPair H).1 * star (diagPair H).1 + (diagPair H).2 * star (diagPair H).2 = 1 := by
  by_cases hw : H 0 1 = 0
  · by_cases hz : 0 ≤ (H 0 0).im <;> simp [diagPair, hw, hz]
  · have hrpos := algAngle_pos_of_ne hw
    rw [diagPair_aa h hw, diagPair_bb hw, ← Complex.ofReal_add]
    have h1 : algAngle H ≠ 0 := ne_of_gt hrpos
    norm_cast
    field_simp
    ring

/-- **THE DIAGONALISATION.** `H = g·psiR r·gᴴ`, `r = algAngle H`, `g = su2Of (diagPair H)`. -/
theorem diag_eq {H : M2} (h : IsSuTwoAlg H) :
    H = su2Of (diagPair H).1 (diagPair H).2 * psiR (algAngle H)
          * (su2Of (diagPair H).1 (diagPair H).2)ᴴ := by
  rw [su2Of_conj_psiR]
  have h11 : H 1 1 = -H 0 0 := suTwoAlg_e11 h
  have h10 : H 1 0 = -(star (H 0 1)) := suTwoAlg_e10 h
  obtain ⟨z, hz⟩ : ∃ z : ℝ, H 0 0 = ((z : ℝ) : ℂ) * Complex.I := ⟨(H 0 0).im, suTwoAlg_e00 h⟩
  have hzim : (H 0 0).im = z := by rw [hz]; simp
  by_cases hw : H 0 1 = 0
  · have hrabs : algAngle H = |z| := by
      rw [algAngle, hw, hzim]
      simp [Real.sqrt_sq_eq_abs]
    have hw10 : H 1 0 = 0 := by rw [h10, hw]; simp
    by_cases hzs : 0 ≤ z
    · have hr : algAngle H = z := by rw [hrabs, abs_of_nonneg hzs]
      have hd : diagPair H = (1, 0) := by
        simp only [diagPair, if_pos hw, hzim, if_pos hzs]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hd, hr, hz, h11, hw, hw10] <;> push_cast <;> ring
    · push_neg at hzs
      have hr : algAngle H = -z := by rw [hrabs, abs_of_neg hzs]
      have hd : diagPair H = (0, 1) := by
        simp only [diagPair, if_pos hw, hzim, if_neg (not_le.mpr hzs)]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hd, hr, hz, h11, hw, hw10] <;> push_cast <;> ring
  · have hrpos := algAngle_pos_of_ne hw
    have hrC : ((algAngle H : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos)
    have h1 : algAngle H ≠ 0 := ne_of_gt hrpos
    have E1 : ((algAngle H : ℝ) : ℂ) * Complex.I *
        ((diagPair H).1 * star (diagPair H).1 - (diagPair H).2 * star (diagPair H).2)
          = H 0 0 := by
      rw [diagPair_aa h hw, diagPair_bb hw, ← Complex.ofReal_sub, hzim, hz]
      have hreal : (algAngle H + z) / (2 * algAngle H)
          - (algAngle H - z) / (2 * algAngle H) = z / algAngle H := by
        field_simp
        ring
      rw [hreal, Complex.ofReal_div]
      field_simp
    have E2 : 2 * ((algAngle H : ℝ) : ℂ) * Complex.I
        * ((diagPair H).1 * star (diagPair H).2) = H 0 1 := by
      rw [diagPair_ab hw]
      have hcast : ((1 / (2 * algAngle H) : ℝ) : ℂ) = 1 / (2 * ((algAngle H : ℝ) : ℂ)) := by
        push_cast; ring
      have hI := Complex.I_mul_I
      rw [hcast]
      field_simp
      linear_combination -hI
    have E3 : 2 * ((algAngle H : ℝ) : ℂ) * Complex.I
        * (star (diagPair H).1 * (diagPair H).2) = H 1 0 := by
      have hs := congrArg star E2
      rw [h10, ← hs]
      simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_conj, map_ofNat]
      ring
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Matrix.head_fin_const]
    · exact E1.symm
    · exact E2.symm
    · exact E3.symm
    · exact h11.trans (congrArg Neg.neg E1.symm)

/-- **THE BRANCH DISCHARGE.** `su2Log (su2Exp H) = H` whenever `H ∈ su(2)` has angle `< π`. -/
theorem su2Log_su2Exp_of_lt_pi {H : M2} (h : IsSuTwoAlg H) (hlt : algAngle H < Real.pi) :
    su2Log (su2Exp H) = H := by
  have hnorm := diagPair_norm h
  set g : SU2 := ⟨su2Of (diagPair H).1 (diagPair H).2, su2Of_mem _ _ hnorm⟩ with hg
  have hgc : (g : M2) = su2Of (diagPair H).1 (diagPair H).2 := rfl
  have hH : H = adMap g (psiR (algAngle H)) := by
    rw [adMap_apply, hgc]
    exact diag_eq h
  have hexp : su2Exp H = g * torus (algAngle H) * g⁻¹ := by
    conv_lhs => rw [hH]
    rw [su2_exp_ad, su2Exp_psiR]
  rw [hexp, su2_log_conj, su2Log_torus (algAngle_nonneg H) hlt, ← hH]

/-- **`hbranch` FROM A CURVATURE BOUND.** `‖H‖_F < √2·π ⟹ hbranch`. -/
theorem branch_of_frobNorm_lt {H : M2} (h : IsSuTwoAlg H)
    (hlt : frobNorm H < Real.sqrt 2 * Real.pi) : su2Log (su2Exp H) = H := by
  refine su2Log_su2Exp_of_lt_pi h ?_
  have heq := frobNorm_eq_sqrt_two_mul_algAngle h
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq] at hlt
  exact lt_of_mul_lt_mul_left (by linarith) (le_of_lt hs2)

/-- **THE ESTIMATE WITH `hbranch` DISCHARGED.**

The only hypothesis beyond §5's is `hsmall : N·β < 2√2`, and `2√2` is the maximum of `‖g − 1‖_F`
on `SU(2)`, attained only at `g = −1`. So the condition says exactly: the level-`l` loop holonomies
`W_x` do not reach the antipode. It is a bound on the INPUT curvature — nothing about the output is
assumed — and it is precisely the quantified form of Balaban's unquantified "for `L²α₀`
sufficiently small". -/
theorem blockedLink_sub_one_le_of_curvature {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ι → SU2)
    (Uc : SU2) (Lreal eps Nplaq beta : ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1)
    (hUc : frobNorm ((Uc : M2) - 1) ≤ Lreal * eps)
    (hloop : ∀ x ∈ s, frobNorm ((W x : M2) - 1) ≤ Nplaq * beta)
    (hsmall : Nplaq * beta < 2 * Real.sqrt 2) :
    frobNorm ((blockedLink s w W Uc : M2) - 1)
      ≤ Lreal * eps + (Real.pi / 2 * Nplaq) * beta := by
  have hlog : ∀ x ∈ s, frobNorm (su2Log (W x)) ≤ (Real.pi / 2) * (Nplaq * beta) := by
    intro x hx
    refine le_trans (frobNorm_su2Log_le_pi_div_two (W x)) ?_
    exact mul_le_mul_of_nonneg_left (hloop x hx) (by positivity)
  have hH : frobNorm (blockExponent s w W) ≤ (Real.pi / 2) * (Nplaq * beta) :=
    frobNorm_blockExponent_le s w W _ hw hsum hlog
  have hpi := Real.pi_pos
  have hlt : frobNorm (blockExponent s w W) < Real.sqrt 2 * Real.pi := by
    have h2 : (Real.pi / 2) * (Nplaq * beta) < (Real.pi / 2) * (2 * Real.sqrt 2) :=
      mul_lt_mul_of_pos_left hsmall (by linarith)
    have : (Real.pi / 2) * (2 * Real.sqrt 2) = Real.sqrt 2 * Real.pi := by ring
    linarith [this ▸ h2]
  exact blockedLink_sub_one_le s w W Uc Lreal eps Nplaq beta hw hsum hUc hloop
    (branch_of_frobNorm_lt (isSuTwoAlg_blockExponent s w W) hlt)

/-- **THE LINK RECURSION, `hbranch` DISCHARGED, ONE `Kb` FOR ALL LEVELS.**
This is the theorem `GammaLevelDefect.hlink` should be replaced by. -/
theorem link_recursion_of_curvature
    (d ell k : ℕ) (eps beta : ℕ → ℝ)
    {ι : Type*} (s : ℕ → Finset ι) (w : ℕ → ι → ℝ) (W : ℕ → ι → SU2) (Uc : ℕ → SU2)
    (hw : ∀ l, ∀ x ∈ s l, 0 ≤ w l x)
    (hsum : ∀ l, ∑ x ∈ s l, w l x = 1)
    (hUc : ∀ l, l < k → frobNorm ((Uc l : M2) - 1) ≤ (ell : ℝ) * eps l)
    (hloop : ∀ l, l < k → ∀ x ∈ s l,
        frobNorm ((W l x : M2) - 1) ≤ (plaqCount d ell : ℝ) * beta l)
    (hsmall : ∀ l, l < k → (plaqCount d ell : ℝ) * beta l < 2 * Real.sqrt 2)
    (hnext : ∀ l, l < k →
        eps (l + 1) ≤ frobNorm ((blockedLink (s l) (w l) (W l) (Uc l) : M2) - 1)) :
    ∀ l, l < k → eps (l + 1) ≤ (ell : ℝ) * eps l + KbConst d ell * beta l := by
  intro l hl
  refine le_trans (hnext l hl) ?_
  have h := blockedLink_sub_one_le_of_curvature (s l) (w l) (W l) (Uc l) (ell : ℝ) (eps l)
    (plaqCount d ell : ℝ) (beta l) (hw l) (hsum l) (hUc l hl) (hloop l hl) (hsmall l hl)
  rw [KbConst]
  exact h

/-! ## §9 — THE ABSTRACT LATTICE STOKES STEP (S5's algebraic half), AND WHAT IS STILL MISSING

S5 says `‖W_x − 1‖ ≤ N(d,L)·β` because `W_x = U(Γ_{c,x})U(c)^{−1}` is a CLOSED-LOOP holonomy. That
splits into two halves:

* **algebraic** — if a holonomy IS an ordered product of conjugated plaquettes, its distance to `1`
  is at most (count)×(curvature). Conjugation is a `frobNorm` isometry and the product telescopes.
  This half is PROVED below.
* **geometric** — that the loop `Γ_{c,x} ∪ (−c)` HAS such a spanning surface, with the count of §6.
  This half needs the lattice, its paths, its plaquettes and the explicit surface. ~~It is NOT built
  here … stated as `loop_is_conj_plaquette_product` — a `sorry` with a name and a locator.~~
  **SUPERSEDED 2026-07-29: it IS built here**, in §11a–§11n, and
  `loop_is_conj_plaquette_product` is `sorry`-free.
  **Nothing in §5–§8 depends on it**: `blockedLink_sub_one_le` and
  `blockedLink_sub_one_le_of_curvature` take S5 as an explicit hypothesis about an abstract
  `loopHol`/`plaqAt`; connecting them to §11's `pathHol`/`plaqHol` is a separate wiring step, which
  is now unblocked but not done.

LAW-19 note: `GammaLevelDefect.frobNorm_prod_sub_one_le` is the same list telescoping. It is NOT
imported, because a concurrent lane holds the write scope on that file and importing it would make
this module's build depend on an in-flight edit. The eight-line re-derivation below is disclosed as
a deliberate duplicate, not an oversight; when the lane lands, this should be deleted in favour of
the import. -/

theorem frobSq_conjTranspose (M : M2) : frobSq Mᴴ = frobSq M := by
  simp only [frobSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  ring

theorem frobSq_mul_left_isometry (W M : M2) (hW : Wᴴ * W = 1) : frobSq (W * M) = frobSq M := by
  have h1 : (W * M)ᴴ = Mᴴ * Wᴴ := Matrix.conjTranspose_mul _ _
  have h2 : Wᴴ * (Wᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hW
  calc frobSq (W * M) = frobSq ((W * M)ᴴ) := (frobSq_conjTranspose _).symm
    _ = frobSq (Mᴴ * Wᴴ) := by rw [h1]
    _ = frobSq Mᴴ := frobSq_mul_right_isometry _ _ h2
    _ = frobSq M := frobSq_conjTranspose _

/-- **Conjugation is a `frobNorm` isometry on `g ↦ g − 1`.** This is why the loop bound is
GAUGE-INVARIANT while the link bound is not. -/
theorem frobNorm_conj_sub_one (g p : SU2) :
    frobNorm (((g * p * g⁻¹ : SU2) : M2) - 1) = frobNorm ((p : M2) - 1) := by
  have hid : (g : M2) * ((p : M2) - 1) * (g : M2)ᴴ = ((g * p * g⁻¹ : SU2) : M2) - 1 := by
    rw [coe_mul, coe_mul, coe_inv, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      mul_star_self g]
  rw [frobNorm, frobNorm, ← hid,
    frobSq_mul_right_isometry _ _
      (by rw [Matrix.conjTranspose_conjTranspose]; exact star_mul_self g),
    frobSq_mul_left_isometry _ _ (star_mul_self g)]

/-- List telescoping (LAW-19 duplicate, disclosed above). -/
theorem frobNorm_prod_sub_one_le (gs : List SU2) (e : ℝ)
    (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ e) :
    frobNorm ((gs.prod : M2) - 1) ≤ (gs.length : ℝ) * e := by
  induction gs with
  | nil =>
    simp only [List.prod_nil, List.length_nil, Nat.cast_zero, zero_mul]
    rw [OneMemClass.coe_one, sub_self]
    exact le_of_eq frobNorm_zero
  | cons g rest ih =>
    have hg : frobNorm ((g : M2) - 1) ≤ e := h g (by simp)
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem g hx))
    rw [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc frobNorm (((g * rest.prod : SU2) : M2) - 1)
        ≤ frobNorm ((g : M2) - 1) + frobNorm ((rest.prod : M2) - 1) :=
          AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _
      _ ≤ e + (rest.length : ℝ) * e := add_le_add hg hrest
      _ = ((rest.length : ℝ) + 1) * e := by ring

/-- **S2 PROVED, given the bond decomposition.** `‖U(c) − 1‖ ≤ L·ε` when the coarse bond `c` is the
ordered product of its `L` fine bonds. This is where the coefficient of `ε` in the recursion comes
from, and it is EXACTLY `ell` — nothing is hidden in it. -/
theorem straight_bond_bound (gs : List SU2) (ell : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hlen : gs.length = ell) (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ eps) :
    frobNorm ((gs.prod : M2) - 1) ≤ (ell : ℝ) * eps := by
  have := frobNorm_prod_sub_one_le gs eps h
  rwa [hlen] at this

/-- **THE ALGEBRAIC HALF OF S5, PROVED.** A holonomy written as an ordered product of conjugated
plaquettes is within (count)×(curvature) of `1`. `q.1` is the transport to the plaquette's corner,
`q.2` the plaquette. -/
theorem frobNorm_conjProd_sub_one_le (ps : List (SU2 × SU2)) (beta : ℝ)
    (h : ∀ q ∈ ps, frobNorm ((q.2 : M2) - 1) ≤ beta) :
    frobNorm ((((ps.map (fun q : SU2 × SU2 => (q.1 * q.2 * q.1⁻¹ : SU2))).prod : SU2) : M2) - 1)
      ≤ (ps.length : ℝ) * beta := by
  have hmap : ∀ g ∈ ps.map (fun q : SU2 × SU2 => (q.1 * q.2 * q.1⁻¹ : SU2)), frobNorm ((g : M2) - 1) ≤ beta := by
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨q, hq, rfl⟩ := hg
    rw [frobNorm_conj_sub_one]
    exact h q hq
  have := frobNorm_prod_sub_one_le _ beta hmap
  rwa [List.length_map] at this

/-- **S5 ASSEMBLED from the algebraic half and §6's count.** Given a spanning surface whose length
is the counted `surfCount`, the loop bound with the counted `plaqCount` follows. -/
theorem loop_bound_of_surface {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (μ : Fin d)
    (hx : ∀ ρ, x ρ ≤ ell - 1) (ps : List (SU2 × SU2)) (beta : ℝ) (hb : 0 ≤ beta)
    (hlen : ps.length = surfCount ell x μ)
    (h : ∀ q ∈ ps, frobNorm ((q.2 : M2) - 1) ≤ beta) :
    frobNorm ((((ps.map (fun q : SU2 × SU2 => (q.1 * q.2 * q.1⁻¹ : SU2))).prod : SU2) : M2) - 1)
      ≤ (plaqCount d ell : ℝ) * beta := by
  refine le_trans (frobNorm_conjProd_sub_one_le ps beta h) ?_
  have hcount : (ps.length : ℝ) ≤ (plaqCount d ell : ℝ) := by
    rw [hlen]
    exact_mod_cast surfCount_le ell x μ hx
  exact mul_le_mul_of_nonneg_right hcount hb

/-! ## §10 — NON-DEGENERACY CONTROL

The smallness class `‖W − 1‖_F < 2√2` is not the identity: it contains genuinely non-central
elements, and the estimate's left-hand side is not forced to `0` there. -/

theorem smallness_class_nontrivial :
    0 < frobNorm (((torus (1 / 2) : SU2) : M2) - 1)
      ∧ frobNorm (((torus (1 / 2) : SU2) : M2) - 1) < 2 * Real.sqrt 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hang : su2Angle (torus (1 / 2)) = 1 / 2 := su2Angle_torus (by norm_num) (by linarith)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hval : frobNorm (((torus (1 / 2) : SU2) : M2) - 1)
      = 2 * Real.sqrt 2 * Real.sin (1 / 4) := by
    rw [frobNorm_sub_one_eq, hang]
    norm_num
  have hsinpos : 0 < Real.sin (1 / 4 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  have hsinlt : Real.sin (1 / 4 : ℝ) < 1 := lt_of_le_of_lt (Real.sin_le (by norm_num)) (by norm_num)
  constructor
  · rw [hval]; positivity
  · rw [hval]; nlinarith

/-! ## §11 — THE LATTICE SURFACE, BUILT (was: the one residual)

Everything above is `sorry`-free, and **so is this section, as of 2026-07-29**. It is imported by
nothing and used by nothing; deleting it changes no other axiom set.

The content: the level-`l` field `V`, a coarse bond `c` in direction `μ` with `c₋` at the origin of
the block, and `x ∈ B(c₋)`. Then the holonomy `V(Γ_{c,x})·V(c)^{−1}` — with `Γ_{c,x}` the p.19
contour `Γ_{c₋,x} ∪ [x,x(c)] ∪ Γ_{x(c),c₊}` — equals the ordered product of `surfCount ell x μ`
conjugated plaquettes of `V`. §6 derives the count; §11 now builds the surface.

~~Discharging it needs: a lattice type with signed steps, path holonomy as a fold, the plaquette,
the cylinder identity by induction on the path, and the pairwise-transposition surface for the
reversal loop. That is ordinary formalisation work … not reached in this lane's budget.~~
**SUPERSEDED: all of it is below.** The road map, in the order it is built:

* §11 head — the lattice `ℤ^d`, signed `Step`s, `stepHol`, `pathHol`, `plaqHol`, `coordSteps`,
  `stairSteps`, `invSteps`, `gammaSteps`, `gammaLoopSteps`;
* §11a — the atomic move: transposing two adjacent forward steps = one plaquette, with a tail;
* §11b–§11f — the counted slides: one step past a leg (`n`), a list past a leg (`n·|p|`), a list
  past a list (`|p|·|q|`);
* §11c — WHY the count erases `μ`, with the over-count trap stated as a lemma;
* §11g — the one-step inverse-path facts;
* §11h — **the path algebra**: `pathEnd`, the append law, `surfProd`, and the relation
  `Deform V n Z W` closed under `trans`/`append_left`/`append_right`, in which the costs ADD;
* §11i — the inverse path cancels for an ARBITRARY path, in any context;
* §11j — the block reversal at exactly `∑_{i<j}|bᵢ||bⱼ|` (`pcL`);
* §11k — the leg to the front at `ell` per non-`μ` step, the `μ`-block free;
* §11l — the two counts identified with `revCount` and `cylCount` exactly;
* §11m — the three segments identified: the return staircase is the path-reverse of the ASCENDING
  staircase, so the loop is `(D ++ L) ++ invSteps (L ++ A)`;
* §11n — the assembly. -/

section Residual

/-! A minimal lattice, just enough to state the residual with the loop holonomy DETERMINED by a
configuration rather than free. (An earlier draft of this section stated it over a free `loopHol`
and a free `plaqAt`; that existential was satisfiable by junk — an S91 defect this lane created and
has now removed. Only the SURFACE is existential here, which is what the statement is about.) -/

/-- Sites of `ℤ^d`. Infinite, so no torus truncation artifact. -/
abbrev LatSite (d : ℕ) : Type := Fin d → ℤ

def shiftS {d : ℕ} (y : LatSite d) (ρ : Fin d) (n : ℤ) : LatSite d := Function.update y ρ (y ρ + n)

/-- A signed step: a direction and an orientation (`true` = forward). -/
abbrev Step (d : ℕ) : Type := Fin d × Bool

def stepEnd {d : ℕ} (y : LatSite d) (e : Step d) : LatSite d :=
  if e.2 then shiftS y e.1 1 else shiftS y e.1 (-1)

def stepHol {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (e : Step d) : SU2 :=
  if e.2 then V y e.1 else (V (shiftS y e.1 (-1)) e.1)⁻¹

/-- Ordered holonomy along a list of signed steps, starting at `y`. -/
def pathHol {d : ℕ} (V : LatSite d → Fin d → SU2) : LatSite d → List (Step d) → SU2
  | _, [] => 1
  | y, e :: rest => stepHol V y e * pathHol V (stepEnd y e) rest

/-- The plaquette holonomy in the `(ρ,ν)` plane at `y`. -/
def plaqHol {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (ρ ν : Fin d) : SU2 :=
  V y ρ * V (shiftS y ρ 1) ν * (V (shiftS y ν 1) ρ)⁻¹ * (V y ν)⁻¹

def coordSteps {d : ℕ} (ρ : Fin d) (n : ℤ) : List (Step d) :=
  List.replicate n.natAbs (ρ, decide (0 ≤ n))

/-- **CMP98 p.24's `Γ_{y,x}`**: one straight segment per direction, coordinate `d` FIRST and
coordinate `1` LAST — the source's descending order, pinned by its own printed consequence
`V₀(x, x+e₁) = 1` (see `lassoCount_dir_one`). -/
def stairSteps {d : ℕ} (y x : LatSite d) : List (Step d) :=
  (List.finRange d).reverse.flatMap (fun ρ => coordSteps ρ (x ρ - y ρ))

/-- Path inversion: reverse the list and flip every orientation. -/
def invSteps {d : ℕ} (p : List (Step d)) : List (Step d) :=
  p.reverse.map (fun e => (e.1, !e.2))

/-- **CMP98 p.19's `Γ_{c,x} = Γ_{c₋,x} ∪ [x, x(c)] ∪ Γ_{x(c),c₊}`**, as a step list from `c₋ = 0`. -/
def gammaSteps {d : ℕ} (ell : ℕ) (μ : Fin d) (x : LatSite d) : List (Step d) :=
  stairSteps 0 x ++ coordSteps μ (ell : ℤ)
    ++ stairSteps (shiftS x μ (ell : ℤ)) (shiftS (0 : LatSite d) μ (ell : ℤ))

/-- The CLOSED loop `Γ_{c,x} ∪ (−c)` whose holonomy is `W_x = U(Γ_{c,x})·U(c)^{−1}`. -/
def gammaLoopSteps {d : ℕ} (ell : ℕ) (μ : Fin d) (x : LatSite d) : List (Step d) :=
  gammaSteps ell μ x ++ invSteps (coordSteps μ (ell : ℤ))

/-! #### §11a — THE ATOMIC MOVE, proved

The reusable core of the residual above, landed separately (main loop, 2026-07-29, after four
dispatched lanes died on transport errors before reaching the file).

**Transposing two adjacent forward steps multiplies the holonomy by exactly one plaquette**, at the
path's own current basepoint. This is the `revCount` half's atomic step: the reversal surface is built
by repeatedly transposing adjacent steps, and each transposition contributes precisely one plaquette
factor — which is why `revCount x = ∑_ν ∑_{ρ<ν} x_ρ x_ν` counts *pairs*.

No hypothesis on `ρ`, `ν` is needed — not even `ρ ≠ ν`. At `ρ = ν` both sides degenerate and
`plaqHol V y ρ ρ = 1` makes it the trivial identity, which is a useful check rather than a defect. -/
theorem pathHol_pair_forward {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (ρ ν : Fin d) :
    pathHol V y [(ρ, true), (ν, true)] = V y ρ * V (shiftS y ρ 1) ν := by
  simp [pathHol, stepHol, stepEnd]

/-- **THE ATOMIC MOVE.** Swapping the order of two adjacent forward steps changes the ordered
holonomy by left-multiplication by the plaquette at the basepoint. Pure group algebra once both sides
are unfolded: the `(V y ν)⁻¹ * V y ν` in the middle cancels, then
`(V (shiftS y ν 1) ρ)⁻¹ * V (shiftS y ν 1) ρ` does. -/
theorem pathHol_transpose_eq_plaq_mul {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d)
    (ρ ν : Fin d) :
    pathHol V y [(ρ, true), (ν, true)]
      = plaqHol V y ρ ν * pathHol V y [(ν, true), (ρ, true)] := by
  rw [pathHol_pair_forward, pathHol_pair_forward, plaqHol]
  group

/-- **The move in conjugated form**, which is the shape `loop_is_conj_plaquette_product`'s list
entries take: transporting the plaquette back along a prefix holonomy `g` conjugates it. -/
theorem pathHol_transpose_conj {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d)
    (ρ ν : Fin d) (g : SU2) :
    g * pathHol V y [(ρ, true), (ν, true)]
      = (g * plaqHol V y ρ ν * g⁻¹) * (g * pathHol V y [(ν, true), (ρ, true)]) := by
  rw [pathHol_transpose_eq_plaq_mul]
  group

/-- **Degenerate check, so the atomic move is not passing for an empty reason.** At `ρ = ν` the
plaquette is trivial and the move says nothing — as it must, since transposing a step with itself is
the identity. A transposition lemma that stayed non-trivial here would be wrong. -/
theorem plaqHol_self {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (ρ : Fin d) :
    plaqHol V y ρ ρ = 1 := by
  rw [plaqHol]
  group

/-- Two forward shifts commute as site maps — including at `ρ = ν`, where both sides are
`update y ρ (y ρ + 2)`. This is what makes the transposed path end at the SAME site, hence share its
tail. -/
theorem shiftS_comm {d : ℕ} (y : LatSite d) (ρ ν : Fin d) :
    shiftS (shiftS y ρ 1) ν 1 = shiftS (shiftS y ν 1) ρ 1 := by
  by_cases h : ρ = ν
  · subst h; rfl
  · funext τ
    simp only [shiftS, Function.update_apply]
    by_cases h1 : τ = ρ <;> by_cases h2 : τ = ν <;>
      simp_all [Function.update_apply]

/-- **THE ATOMIC MOVE, WITH A TAIL — the form every induction actually consumes.**

Transposing the first two forward steps of *any* path multiplies its holonomy by exactly one
plaquette, and the tail is untouched: by `shiftS_comm` the two orders reach the same site, so the
suffix contributes the identical factor on both sides.

This is the generalization `pathHol_transpose_eq_plaq_mul` lacked. The cylinder induction slides one
staircase step along `coordSteps μ ell` by applying this `ell` times (hence `cylCount`'s factor of
`ell`), and the reversal half applies it once per crossing pair (hence `revCount`'s `x_ρ · x_ν`). -/
theorem pathHol_transpose_cons {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d)
    (ρ ν : Fin d) (rest : List (Step d)) :
    pathHol V y ((ρ, true) :: (ν, true) :: rest)
      = plaqHol V y ρ ν * pathHol V y ((ν, true) :: (ρ, true) :: rest) := by
  have hL : pathHol V y ((ρ, true) :: (ν, true) :: rest)
      = (V y ρ * V (shiftS y ρ 1) ν) * pathHol V (shiftS (shiftS y ρ 1) ν 1) rest := by
    simp [pathHol, stepHol, stepEnd, mul_assoc]
  have hR : pathHol V y ((ν, true) :: (ρ, true) :: rest)
      = (V y ν * V (shiftS y ν 1) ρ) * pathHol V (shiftS (shiftS y ν 1) ρ 1) rest := by
    simp [pathHol, stepHol, stepEnd, mul_assoc]
  rw [hL, hR, ← shiftS_comm y ρ ν, plaqHol]
  group

/-! #### §11b — THE CYLINDER SLIDE

Dragging one forward step along `coordSteps μ n` costs **exactly `n`** conjugated plaquettes. This is
the cylinder half's engine, and it is where `cylCount ell x μ = ell * ∑_{ρ≠μ} x ρ` gets its factor of
`ell`: each of the `∑ x ρ` staircase steps is dragged the full length `ell` of the `μ`-leg.

Two small lemmas first, then the induction. -/

/-- `coordSteps` at a successor peels one forward step off the front. -/
theorem coordSteps_succ {d : ℕ} (μ : Fin d) (n : ℕ) :
    coordSteps μ ((n + 1 : ℕ) : ℤ) = (μ, true) :: coordSteps μ ((n : ℕ) : ℤ) := by
  have hd1 : decide ((0 : ℤ) ≤ (n : ℤ) + 1) = true := decide_eq_true (by positivity)
  have hd2 : decide ((0 : ℤ) ≤ ((n : ℕ) : ℤ)) = true := decide_eq_true (Int.natCast_nonneg _)
  have habs : ((n : ℤ) + 1).natAbs = n + 1 := by omega
  simp only [coordSteps, Nat.cast_add, Nat.cast_one, hd1, hd2, habs, Int.natAbs_natCast]
  exact List.replicate_succ

/-- **Conjugation distributes over the surface product.** Left-multiplying every conjugator by a
fixed `g` conjugates the whole product by `g`. This is the bookkeeping that lets the slide induction
carry its accumulated surface past one more step of the `μ`-leg. -/
theorem conj_prod_map {d : ℕ} (V : LatSite d → Fin d → SU2) (g : SU2)
    (ps : List (SU2 × (LatSite d × Fin d × Fin d))) :
    ((ps.map (fun q => (g * q.1, q.2))).map
        (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod
      = g * (ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod * g⁻¹ := by
  induction ps with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      group

/-- **THE CYLINDER SLIDE.** Moving a forward `ρ`-step from the front of `coordSteps μ n ++ rest` to
after the `μ`-leg costs exactly `n` conjugated plaquettes — no more, no fewer.

The induction is the atomic move plus `conj_prod_map`: at each step the plaquette at the current site
is prepended with a trivial conjugator, and every plaquette already accumulated gets its conjugator
left-multiplied by the `μ`-link just crossed. -/
theorem slide_step_along_coordSteps {d : ℕ} (V : LatSite d → Fin d → SU2)
    (ρ μ : Fin d) (n : ℕ) : ∀ (y : LatSite d) (rest : List (Step d)),
    ∃ ps : List (SU2 × (LatSite d × Fin d × Fin d)),
      ps.length = n ∧
      pathHol V y ((ρ, true) :: (coordSteps μ ((n : ℕ) : ℤ) ++ rest))
        = (ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod
          * pathHol V y (coordSteps μ ((n : ℕ) : ℤ) ++ (ρ, true) :: rest) := by
  induction n with
  | zero =>
      intro y rest
      refine ⟨[], rfl, ?_⟩
      simp [coordSteps]
  | succ m ih =>
      intro y rest
      obtain ⟨ps, hlen, hps⟩ := ih (shiftS y μ 1) rest
      refine ⟨(1, (y, ρ, μ)) :: ps.map (fun q => (V y μ * q.1, q.2)), ?_, ?_⟩
      · simp [hlen]
      · have hstep : pathHol V y ((ρ, true) :: (coordSteps μ ((m + 1 : ℕ) : ℤ) ++ rest))
            = plaqHol V y ρ μ * (V y μ *
                pathHol V (shiftS y μ 1) ((ρ, true) :: (coordSteps μ ((m : ℕ) : ℤ) ++ rest))) := by
          rw [coordSteps_succ]
          rw [show ((ρ, true) :: ((μ, true) :: coordSteps μ ((m : ℕ) : ℤ) ++ rest))
                = (ρ, true) :: (μ, true) :: (coordSteps μ ((m : ℕ) : ℤ) ++ rest) from rfl]
          rw [pathHol_transpose_cons]
          simp [pathHol, stepHol, stepEnd, mul_assoc]
        have hrhs : pathHol V y (coordSteps μ ((m + 1 : ℕ) : ℤ) ++ (ρ, true) :: rest)
            = V y μ * pathHol V (shiftS y μ 1)
                (coordSteps μ ((m : ℕ) : ℤ) ++ (ρ, true) :: rest) := by
          rw [coordSteps_succ]
          simp [pathHol, stepHol, stepEnd, mul_assoc]
        rw [hstep, hps, hrhs, List.map_cons, List.prod_cons, conj_prod_map]
        group

/-! #### §11c — WHY THE COUNT EXCLUDES `μ`, and why that is not an accident

`cylCount ell x μ = ell * ∑_{ρ ∈ univ.erase μ} x ρ` — the sum **erases `μ`**. But `stairSteps 0 x`
runs over *every* direction including `μ`, so the assembly must charge **zero** plaquettes for the
`μ`-component of the staircase, while `slide_step_along_coordSteps` charges `n` for a generic step.

Both facts are true and they do not conflict, because a `μ`-step at the head of the `μ`-leg does not
need sliding at all — it simply **extends the leg**. That is the content below, and it is the exact
point at which an assembly could silently over-count by `ell * x μ`: applying the generic slide to
the `μ`-direction would produce `ell` list entries whose plaquettes are all trivial by
`plaqHol_self`, and the product would still be correct while the LENGTH would exceed `surfCount`.
Since the residual demands the length **exactly**, an over-count is unrecoverable rather than merely
wasteful: entries can be ADDED to a surface list for free but never REMOVED.

~~padding is impossible (every entry contributes a conjugated plaquette, never an inverse)~~
**CORRECTED 2026-07-29: that reason is false, and `mu_slide_entries_are_trivial` immediately below
proves it.** An entry `(g, (y, ρ, ρ))` contributes `g·plaqHol V y ρ ρ·g⁻¹ = 1`, so for `d ≥ 1` any
surface list can be padded UPWARD by trivial diagonal entries at no cost — which means
`∃ ps, ps.length = N ∧ …` is equivalent to `∃ ps, ps.length ≤ N ∧ …`, and the exact-length form is
not the strong statement this comment claimed. The operational conclusion is unaffected (padding is
monotone: up, never down), and the assembly in §11n hits `surfCount` exactly with no padding at all.

Recorded as a lemma rather than a comment so the assembly cannot take the wrong branch silently. -/

/-- **A `μ`-step at the head of the `μ`-leg is FREE**: it extends the leg, costing no plaquette. This
is the branch the assembly must take for the `μ`-component of `stairSteps`, and it is why
`cylCount`'s sum erases `μ`. -/
theorem mu_step_extends_leg {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (μ : Fin d)
    (n : ℕ) (rest : List (Step d)) :
    pathHol V y ((μ, true) :: (coordSteps μ ((n : ℕ) : ℤ) ++ rest))
      = pathHol V y (coordSteps μ ((n + 1 : ℕ) : ℤ) ++ rest) := by
  rw [coordSteps_succ]
  rfl

/-- **The over-count trap, made explicit.** The generic slide applied in the `μ`-direction is not
*wrong* — its product identity holds — but every plaquette it emits is trivial, so it inflates the
list length while contributing nothing. Stated so that a future assembly comparing its total against
`surfCount` can see immediately which branch it must have taken. -/
theorem mu_slide_entries_are_trivial {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d)
    (μ : Fin d) (g : SU2) :
    g * plaqHol V y μ μ * g⁻¹ = 1 := by
  rw [plaqHol_self]
  group

/-! #### §11d — SLIDING A WHOLE LIST PAST THE LEG

The cylinder half needs the whole staircase moved past the `μ`-leg, not one step. The cost multiplies:
a list of `p.length` forward steps costs exactly `n * p.length`.

Induction on `p`, using `slide_step_along_coordSteps` for the head and `conj_prod_map` to carry the
tail's accumulated surface past the head's link. -/

/-- **THE LIST SLIDE.** Moving a list of forward steps from before the `μ`-leg to after it costs
exactly `n * p.length` conjugated plaquettes.

Note the shape of the count: **multiplicative**, one factor of `n` per step. Composed with
`stairSteps`'s decomposition this is what produces `cylCount`'s `ell * ∑ x ρ` — and the `μ`-component
must be routed through `mu_step_extends_leg` instead, or the total over-counts (§11c). -/
theorem slide_list_along_coordSteps {d : ℕ} (V : LatSite d → Fin d → SU2) (μ : Fin d) (n : ℕ) :
    ∀ (p : List (Step d)), (∀ e ∈ p, e.2 = true) →
    ∀ (y : LatSite d) (rest : List (Step d)),
    ∃ ps : List (SU2 × (LatSite d × Fin d × Fin d)),
      ps.length = n * p.length ∧
      pathHol V y (p ++ (coordSteps μ ((n : ℕ) : ℤ) ++ rest))
        = (ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod
          * pathHol V y (coordSteps μ ((n : ℕ) : ℤ) ++ (p ++ rest)) := by
  intro p
  induction p with
  | nil =>
      intro _ y rest
      exact ⟨[], by simp, by simp⟩
  | cons e t ih =>
      obtain ⟨a, b⟩ := e
      cases b
      case false =>
        intro hfwd
        exact absurd (hfwd (a, false) (by simp)) (by simp)
      case true =>
      intro hfwd y rest
      have hfwd_t : ∀ f ∈ t, f.2 = true := fun f hf => hfwd f (by simp [hf])
      -- slide the tail past the leg, starting one step in
      obtain ⟨pt, hptlen, hpt⟩ := ih hfwd_t (stepEnd y (a, true)) rest
      -- then slide the head past the leg
      obtain ⟨pe, hpelen, hpe⟩ := slide_step_along_coordSteps V a μ n y (t ++ rest)
      refine ⟨pt.map (fun q => (stepHol V y (a, true) * q.1, q.2)) ++ pe, ?_, ?_⟩
      · simp only [List.length_append, List.length_map, hptlen, hpelen, List.length_cons]
        ring
      · -- unfold the head step on both the source and the slid form
        have hkey : stepHol V y (a, true) *
              pathHol V (stepEnd y (a, true)) (coordSteps μ ((n : ℕ) : ℤ) ++ (t ++ rest))
            = (pe.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod
              * pathHol V y (coordSteps μ ((n : ℕ) : ℤ) ++ ((a, true) :: (t ++ rest))) := by
          have := hpe
          simp only [pathHol] at this
          exact this
        have hL : pathHol V y (((a, true) :: t) ++ (coordSteps μ ((n : ℕ) : ℤ) ++ rest))
            = stepHol V y (a, true) *
              pathHol V (stepEnd y (a, true)) (t ++ (coordSteps μ ((n : ℕ) : ℤ) ++ rest)) := by
          simp only [List.cons_append, pathHol]
        rw [hL, hpt]
        rw [show pathHol V y (coordSteps μ ((n : ℕ) : ℤ) ++ (((a, true) :: t) ++ rest))
              = pathHol V y (coordSteps μ ((n : ℕ) : ℤ) ++ ((a, true) :: (t ++ rest))) by
            simp]
        rw [List.map_append, List.prod_append, conj_prod_map]
        rw [show stepHol V y (a, true) *
              ((pt.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod *
                pathHol V (stepEnd y (a, true)) (coordSteps μ ((n : ℕ) : ℤ) ++ (t ++ rest)))
            = (stepHol V y (a, true) *
                (pt.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod *
                (stepHol V y (a, true))⁻¹) *
              (stepHol V y (a, true) *
                pathHol V (stepEnd y (a, true)) (coordSteps μ ((n : ℕ) : ℤ) ++ (t ++ rest))) from by
            group]
        rw [hkey]
        group

/-! #### §11e — THE STAIRCASE'S LENGTH AND ORIENTATION

The list slide charges `n * p.length`, so the assembly's count is exact only if `p.length` is known
exactly. `stairSteps` is a `flatMap` of per-direction legs, so its length is the sum of the legs'.

Proved here, together with the all-forward hypothesis the slide requires. Both are needed before any
count can be compared against `surfCount`, and together they make the global picture visible:

* `cylCount ell x μ = ell * ∑_{ρ≠μ} x ρ` is the cost of sliding the **non-`μ`** part of the staircase
  past the leg — `ell` per step, by the list slide;
* `revCount x = ∑_{ρ<ν} x ρ * x ν` is the cost of **reordering** the staircase so the `μ`-leg becomes
  adjacent to the main leg (and can then merge for free by `mu_step_extends_leg`) — one transposition
  per crossing pair, by the atomic move.

That is why `surfCount` is their sum, and it is the first time the two counts have been given a single
geometric reading in this file. -/

/-- The length of a coordinate leg is the absolute value of its signed extent. -/
theorem coordSteps_length {d : ℕ} (ρ : Fin d) (m : ℤ) :
    (coordSteps ρ m).length = m.natAbs := by
  simp [coordSteps]

/-- **The staircase's length is the sum of its legs'** — the exact input the list slide's
`n * p.length` needs. -/
theorem stairSteps_length {d : ℕ} (y x : LatSite d) :
    (stairSteps y x).length
      = (((List.finRange d).reverse.map (fun ρ => (x ρ - y ρ).natAbs)).sum) := by
  simp [stairSteps, List.length_flatMap, coordSteps_length]

/-- **Every step of a coordinate leg is forward when its extent is nonnegative.** -/
theorem coordSteps_forward {d : ℕ} (ρ : Fin d) {m : ℤ} (hm : 0 ≤ m) :
    ∀ e ∈ coordSteps ρ m, e.2 = true := by
  intro e he
  have := List.eq_of_mem_replicate he
  simp [coordSteps, this, decide_eq_true hm]

/-- **Every step of the staircase is forward when the target dominates the source coordinatewise** —
the hypothesis `slide_list_along_coordSteps` requires. -/
theorem stairSteps_forward {d : ℕ} {y x : LatSite d} (h : ∀ ρ, y ρ ≤ x ρ) :
    ∀ e ∈ stairSteps y x, e.2 = true := by
  intro e he
  rw [stairSteps, List.mem_flatMap] at he
  obtain ⟨ρ, _, hmem⟩ := he
  exact coordSteps_forward ρ (by have := h ρ; omega) e hmem

/-! #### §11f — THE GENERAL BLOCK SWAP

`slide_list_along_coordSteps` moves a list past a **single-direction leg**. The reversal half needs
more: it must move a list past *another arbitrary list*, because reversing the staircase's
per-direction leg order is a sequence of block swaps between legs of different directions.

The general statement is cleaner than either special case and subsumes both:

> swapping two adjacent blocks of forward steps costs exactly `p.length * q.length` plaquettes.

Two inductions. First a list past one step (cost `p.length`, head handled by the atomic move), then a
list past a list (cost `p.length * q.length`, each step of `q` handled by the first).

**This is where `revCount = ∑_{ρ<ν} x_ρ x_ν` comes from**, and the reading is now forced rather than
asserted: reversing the order of blocks of sizes `x_ρ` requires swapping every unordered pair exactly
once, and each swap of blocks of sizes `x_ρ`, `x_ν` costs `x_ρ * x_ν`. Sum over pairs. -/

/-- **A list past ONE step**, at exactly `p.length` plaquettes. -/
theorem slide_list_past_step {d : ℕ} (V : LatSite d → Fin d → SU2) (b : Fin d) :
    ∀ (p : List (Step d)), (∀ e ∈ p, e.2 = true) →
    ∀ (y : LatSite d) (rest : List (Step d)),
    ∃ ps : List (SU2 × (LatSite d × Fin d × Fin d)),
      ps.length = p.length ∧
      pathHol V y (p ++ ((b, true) :: rest))
        = (ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod
          * pathHol V y ((b, true) :: (p ++ rest)) := by
  intro p
  induction p with
  | nil => intro _ y rest; exact ⟨[], by simp, by simp⟩
  | cons e t ih =>
      obtain ⟨a, bb⟩ := e
      cases bb
      case false =>
        intro hfwd
        exact absurd (hfwd (a, false) (by simp)) (by simp)
      case true =>
      intro hfwd y rest
      have hfwd_t : ∀ f ∈ t, f.2 = true := fun f hf => hfwd f (by simp [hf])
      obtain ⟨pt, hptlen, hpt⟩ := ih hfwd_t (stepEnd y (a, true)) rest
      refine ⟨pt.map (fun q => (stepHol V y (a, true) * q.1, q.2)) ++ [(1, (y, a, b))], ?_, ?_⟩
      · simp [hptlen, Nat.add_comm]
      · have hcomb : stepHol V y (a, true) *
              pathHol V (stepEnd y (a, true)) ((b, true) :: (t ++ rest))
            = plaqHol V y a b * pathHol V y ((b, true) :: ((a, true) :: (t ++ rest))) := by
          have h := pathHol_transpose_cons V y a b (t ++ rest)
          simp only [pathHol] at h
          exact h
        have hL : pathHol V y (((a, true) :: t) ++ ((b, true) :: rest))
            = stepHol V y (a, true) *
              pathHol V (stepEnd y (a, true)) (t ++ ((b, true) :: rest)) := by
          simp only [List.cons_append, pathHol]
        rw [hL, hpt]
        rw [show pathHol V y ((b, true) :: (((a, true) :: t) ++ rest))
              = pathHol V y ((b, true) :: ((a, true) :: (t ++ rest))) by simp]
        rw [show stepHol V y (a, true) *
              ((pt.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod *
                pathHol V (stepEnd y (a, true)) ((b, true) :: (t ++ rest)))
            = (stepHol V y (a, true) *
                (pt.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod *
                (stepHol V y (a, true))⁻¹) *
              (stepHol V y (a, true) *
                pathHol V (stepEnd y (a, true)) ((b, true) :: (t ++ rest))) from by group]
        rw [hcomb, List.map_append, List.prod_append, conj_prod_map]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        group

/-- **THE GENERAL BLOCK SWAP.** Two adjacent blocks of forward steps exchange at exactly
`p.length * q.length` conjugated plaquettes.

`slide_list_along_coordSteps` is the special case `q = coordSteps μ n`. This is the form the reversal
half consumes, and the product `p.length * q.length` is literally `x_ρ * x_ν` when the blocks are the
`ρ`- and `ν`-legs of the staircase. -/
theorem slide_list_past_list {d : ℕ} (V : LatSite d → Fin d → SU2) :
    ∀ (q p : List (Step d)), (∀ e ∈ p, e.2 = true) → (∀ f ∈ q, f.2 = true) →
    ∀ (y : LatSite d) (rest : List (Step d)),
    ∃ ps : List (SU2 × (LatSite d × Fin d × Fin d)),
      ps.length = p.length * q.length ∧
      pathHol V y (p ++ (q ++ rest))
        = (ps.map (fun r => r.1 * plaqHol V r.2.1 r.2.2.1 r.2.2.2 * r.1⁻¹)).prod
          * pathHol V y (q ++ (p ++ rest)) := by
  intro q
  induction q with
  | nil => intro p _ _ y rest; exact ⟨[], by simp, by simp⟩
  | cons f q' ih =>
      obtain ⟨c, cb⟩ := f
      cases cb
      case false =>
        intro p _ hfq
        exact absurd (hfq (c, false) (by simp)) (by simp)
      case true =>
      intro p hfp hfq y rest
      have hfq' : ∀ g ∈ q', g.2 = true := fun g hg => hfq g (by simp [hg])
      -- first move p past the single head step c, then past the remaining block q'
      obtain ⟨p1, hp1len, hp1⟩ := slide_list_past_step V c p hfp y (q' ++ rest)
      obtain ⟨p2, hp2len, hp2⟩ := ih p hfp hfq' (stepEnd y (c, true)) rest
      refine ⟨p1 ++ p2.map (fun r => (stepHol V y (c, true) * r.1, r.2)), ?_, ?_⟩
      · simp only [List.length_append, List.length_map, hp1len, hp2len, List.length_cons]
        ring
      · have hA : pathHol V y ((c, true) :: (p ++ (q' ++ rest)))
            = stepHol V y (c, true) *
              ((p2.map (fun r => r.1 * plaqHol V r.2.1 r.2.2.1 r.2.2.2 * r.1⁻¹)).prod *
                pathHol V (stepEnd y (c, true)) (q' ++ (p ++ rest))) := by
          rw [show pathHol V y ((c, true) :: (p ++ (q' ++ rest)))
                = stepHol V y (c, true) *
                  pathHol V (stepEnd y (c, true)) (p ++ (q' ++ rest)) from by
            simp only [pathHol]]
          rw [hp2]
        have hB : pathHol V y ((c, true) :: (q' ++ (p ++ rest)))
            = stepHol V y (c, true) *
              pathHol V (stepEnd y (c, true)) (q' ++ (p ++ rest)) := by
          simp only [pathHol]
        rw [show p ++ (((c, true) :: q') ++ rest) = p ++ ((c, true) :: (q' ++ rest)) by simp]
        rw [show ((c, true) :: q') ++ (p ++ rest) = (c, true) :: (q' ++ (p ++ rest)) by simp]
        rw [hp1, hA, hB, List.map_append, List.prod_append, conj_prod_map]
        group

/-! #### §11g — INVERSE PATHS

The loop has two backward pieces: `invSteps (coordSteps μ ell)` closing it, and the return staircase,
whose steps run negative. The slide lemmas require forward steps, so the assembly must convert both.

The governing fact is that walking a step backwards from its own endpoint inverts its holonomy. -/

/-- A forward shift followed by its backward shift is the identity on sites. -/
theorem shiftS_cancel {d : ℕ} (y : LatSite d) (ρ : Fin d) :
    shiftS (shiftS y ρ 1) ρ (-1) = y := by
  funext τ
  by_cases h : τ = ρ
  · subst h; simp [shiftS]
  · simp [shiftS, Function.update_apply, h]

/-- **Walking one step backwards from its endpoint inverts its holonomy.** The base-site shift by
`-1` inside `stepHol`'s inverse branch is exactly what makes this come out — which is why that branch
was the delicate point of the atomic move. -/
theorem stepHol_back {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (a : Fin d) :
    stepHol V (stepEnd y (a, true)) (a, false) = (stepHol V y (a, true))⁻¹ := by
  simp only [stepHol, stepEnd, if_true, if_false, Bool.false_eq_true]
  rw [shiftS_cancel]

/-- **`invSteps` of a single forward step, walked from its endpoint, inverts it.** The one-step case
of the inverse-path identity, and the base of the induction the assembly's two backward pieces need. -/
theorem pathHol_invSteps_single {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (a : Fin d) :
    pathHol V (stepEnd y (a, true)) (invSteps [(a, true)]) = (stepHol V y (a, true))⁻¹ := by
  simp only [invSteps, List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
    List.map_nil, Bool.not_true, pathHol]
  rw [stepHol_back]
  group

/-- **A forward step followed immediately by its own inverse contributes nothing** — the cancellation
the loop's closing leg performs against the outbound leg, at the level of one step. -/
theorem pathHol_step_then_back {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (a : Fin d)
    (rest : List (Step d)) :
    pathHol V y ((a, true) :: (a, false) :: rest) = pathHol V y rest := by
  simp only [pathHol, stepHol, stepEnd, if_true, if_false, Bool.false_eq_true, shiftS_cancel]
  group

/-! #### §11h — PATH ALGEBRA: endpoints, appends, and the DEFORMATION RELATION

Each engine of §11a–§11g carries its own explicit `rest` and its own explicit surface list, which
makes every composition a hand-rolled rewrite. This subsection replaces that with an algebra: the
endpoint of a path, the append law for `pathHol`, and a relation

> `Deform V n Z W` — *`Z` and `W` have the same ordered holonomy in EVERY context (every basepoint,
> every suffix), up to a left factor which is a product of exactly `n` conjugated plaquettes.*

`Deform` is transitive and closed under appending a block on either side, so the assembly below is
composition in this algebra rather than rewriting. The count adds under composition, which is what
makes "exactly `surfCount`" checkable term by term. -/

/-- The endpoint of a path started at `y`. -/
def pathEnd {d : ℕ} : LatSite d → List (Step d) → LatSite d
  | y, [] => y
  | y, e :: rest => pathEnd (stepEnd y e) rest

theorem pathEnd_append {d : ℕ} (p q : List (Step d)) :
    ∀ y : LatSite d, pathEnd y (p ++ q) = pathEnd (pathEnd y p) q := by
  induction p with
  | nil => intro y; rfl
  | cons e t ih => intro y; simp only [List.cons_append, pathEnd]; exact ih _

/-- **The append law for the ordered holonomy.** -/
theorem pathHol_append {d : ℕ} (V : LatSite d → Fin d → SU2) (p q : List (Step d)) :
    ∀ y : LatSite d, pathHol V y (p ++ q) = pathHol V y p * pathHol V (pathEnd y p) q := by
  induction p with
  | nil => intro y; simp only [List.nil_append, pathHol, pathEnd, one_mul]
  | cons e t ih =>
      intro y
      simp only [List.cons_append, pathHol, pathEnd, ih, mul_assoc]

/-- The ordered product of a list of conjugated plaquettes — the right-hand side shape of the
residual and of every slide lemma above. -/
def surfProd {d : ℕ} (V : LatSite d → Fin d → SU2)
    (ps : List (SU2 × (LatSite d × Fin d × Fin d))) : SU2 :=
  (ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod

theorem surfProd_nil {d : ℕ} (V : LatSite d → Fin d → SU2) : surfProd V [] = 1 := by
  simp [surfProd]

theorem surfProd_append {d : ℕ} (V : LatSite d → Fin d → SU2)
    (ps qs : List (SU2 × (LatSite d × Fin d × Fin d))) :
    surfProd V (ps ++ qs) = surfProd V ps * surfProd V qs := by
  simp [surfProd, List.prod_append]

theorem surfProd_conj {d : ℕ} (V : LatSite d → Fin d → SU2) (g : SU2)
    (ps : List (SU2 × (LatSite d × Fin d × Fin d))) :
    surfProd V (ps.map (fun q => (g * q.1, q.2))) = g * surfProd V ps * g⁻¹ :=
  conj_prod_map V g ps

/-- **THE DEFORMATION RELATION.** `Deform V n Z W` says the step list `Z` can be deformed to `W`
at a cost of exactly `n` conjugated plaquettes of `V`, uniformly in the basepoint and in any
suffix. Note that the plaquette factor sits on the LEFT, which is what lets a prefix be absorbed by
conjugation (`Deform.append_left`). -/
def Deform {d : ℕ} (V : LatSite d → Fin d → SU2) (n : ℕ) (Z W : List (Step d)) : Prop :=
  ∀ (y : LatSite d) (rest : List (Step d)),
    ∃ ps : List (SU2 × (LatSite d × Fin d × Fin d)),
      ps.length = n ∧ pathHol V y (Z ++ rest) = surfProd V ps * pathHol V y (W ++ rest)

/-- Equal step lists deform into one another for free. This is the branch that pays ZERO, and it is
the one the `μ`-block must take (§11c). -/
theorem Deform.of_eq {d : ℕ} (V : LatSite d → Fin d → SU2) {Z W : List (Step d)} (h : Z = W) :
    Deform V 0 Z W := fun _ _ => ⟨[], rfl, by rw [h, surfProd_nil, one_mul]⟩

/-- Rewriting a `Deform` along equalities of its count and its endpoints. -/
theorem Deform.conv {d : ℕ} {V : LatSite d → Fin d → SU2} {n m : ℕ} {Z W Z' W' : List (Step d)}
    (h : Deform V n Z W) (hn : n = m) (hZ : Z = Z') (hW : W = W') : Deform V m Z' W' := by
  rw [← hn, ← hZ, ← hW]; exact h

/-- **The costs ADD along a composition.** -/
theorem Deform.trans {d : ℕ} {V : LatSite d → Fin d → SU2} {n m : ℕ} {Z W X : List (Step d)}
    (h₁ : Deform V n Z W) (h₂ : Deform V m W X) : Deform V (n + m) Z X := by
  intro y rest
  obtain ⟨ps, hps, hp⟩ := h₁ y rest
  obtain ⟨qs, hqs, hq⟩ := h₂ y rest
  exact ⟨ps ++ qs, by simp [hps, hqs], by rw [hp, hq, surfProd_append, mul_assoc]⟩

/-- Appending a block on the RIGHT is free: the suffix is already universally quantified. -/
theorem Deform.append_right {d : ℕ} {V : LatSite d → Fin d → SU2} {n : ℕ} {Z W : List (Step d)}
    (h : Deform V n Z W) (r : List (Step d)) : Deform V n (Z ++ r) (W ++ r) := by
  intro y rest
  obtain ⟨ps, hps, hp⟩ := h y (r ++ rest)
  exact ⟨ps, hps, by simpa only [List.append_assoc] using hp⟩

/-- Appending a block on the LEFT costs nothing either, but the surface must be TRANSPORTED: every
conjugator is left-multiplied by the prefix holonomy. This is `conj_prod_map`'s reason for
existing. -/
theorem Deform.append_left {d : ℕ} {V : LatSite d → Fin d → SU2} {n : ℕ} {Z W : List (Step d)}
    (h : Deform V n Z W) (p : List (Step d)) : Deform V n (p ++ Z) (p ++ W) := by
  intro y rest
  obtain ⟨ps, hps, hp⟩ := h (pathEnd y p) rest
  refine ⟨ps.map (fun q => (pathHol V y p * q.1, q.2)), by simpa using hps, ?_⟩
  simp only [List.append_assoc]
  rw [pathHol_append V p (Z ++ rest) y, pathHol_append V p (W ++ rest) y, hp, surfProd_conj]
  group

/-- §11f's block swap, in `Deform` form. -/
theorem deform_swap {d : ℕ} (V : LatSite d → Fin d → SU2) (p q : List (Step d))
    (hp : ∀ e ∈ p, e.2 = true) (hq : ∀ f ∈ q, f.2 = true) :
    Deform V (p.length * q.length) (p ++ q) (q ++ p) := by
  intro y rest
  obtain ⟨ps, hps, hp'⟩ := slide_list_past_list V q p hp hq y rest
  exact ⟨ps, hps, by simpa only [List.append_assoc, surfProd] using hp'⟩

/-- §11d's cylinder slide, in `Deform` form. The count is `n` PER STEP of `p`; this is the only
place the factor `ell` of `cylCount` enters. -/
theorem deform_leg {d : ℕ} (V : LatSite d → Fin d → SU2) (μ : Fin d) (n : ℕ) (p : List (Step d))
    (hp : ∀ e ∈ p, e.2 = true) :
    Deform V (n * p.length) (p ++ coordSteps μ ((n : ℕ) : ℤ))
      (coordSteps μ ((n : ℕ) : ℤ) ++ p) := by
  intro y rest
  obtain ⟨ps, hps, hp'⟩ := slide_list_along_coordSteps V μ n p hp y rest
  exact ⟨ps, hps, by simpa only [List.append_assoc, surfProd] using hp'⟩

/-! #### §11i — THE INVERSE PATH, for an ARBITRARY path

§11g proves the one-step cancellation. The loop's two backward pieces are whole blocks, so the
cancellation is needed for an arbitrary path and in an arbitrary context. It is what lets the
right-hand side of the residual be the bare surface product with no trailing holonomy. -/

theorem shiftS_add {d : ℕ} (y : LatSite d) (ρ : Fin d) (m n : ℤ) :
    shiftS (shiftS y ρ m) ρ n = shiftS y ρ (m + n) := by
  simp only [shiftS, Function.update_idem, Function.update_self]
  rw [add_assoc]

theorem shiftS_zero {d : ℕ} (y : LatSite d) (ρ : Fin d) : shiftS y ρ 0 = y := by
  simp [shiftS]

/-- Walking a step and then its reverse returns to the same SITE, in both orientations. -/
theorem stepEnd_flip {d : ℕ} (y : LatSite d) (e : Step d) :
    stepEnd (stepEnd y e) (e.1, !e.2) = y := by
  obtain ⟨a, b⟩ := e
  cases b
  · simp only [stepEnd, Bool.not_false, if_true, if_false, Bool.false_eq_true, shiftS_add]
    norm_num [shiftS_zero]
  · simp only [stepEnd, Bool.not_true, if_true, if_false, Bool.false_eq_true, shiftS_add]
    norm_num [shiftS_zero]

/-- Walking a step and then its reverse INVERTS its holonomy, in both orientations. The forward case
is §11g's `stepHol_back`; the backward case is where `stepHol`'s `-1` base shift pays off. -/
theorem stepHol_flip {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d) (e : Step d) :
    stepHol V (stepEnd y e) (e.1, !e.2) = (stepHol V y e)⁻¹ := by
  obtain ⟨a, b⟩ := e
  cases b
  · simp only [stepEnd, stepHol, Bool.not_false, if_true, if_false, Bool.false_eq_true, inv_inv]
  · exact stepHol_back V y a

theorem invSteps_cons {d : ℕ} (e : Step d) (t : List (Step d)) :
    invSteps (e :: t) = invSteps t ++ [(e.1, !e.2)] := by
  simp [invSteps]

theorem invSteps_append {d : ℕ} (p q : List (Step d)) :
    invSteps (p ++ q) = invSteps q ++ invSteps p := by
  simp [invSteps]

/-- **THE INVERSE PATH CANCELS, IN ANY CONTEXT.** -/
theorem pathHol_cancel_invSteps {d : ℕ} (V : LatSite d → Fin d → SU2) :
    ∀ (p : List (Step d)) (y : LatSite d) (rest : List (Step d)),
      pathHol V y (p ++ invSteps p ++ rest) = pathHol V y rest := by
  intro p
  induction p with
  | nil => intro y rest; simp [invSteps]
  | cons e t ih =>
      intro y rest
      rw [invSteps_cons,
        show (e :: t) ++ (invSteps t ++ [(e.1, !e.2)]) ++ rest
            = e :: ((t ++ invSteps t) ++ ((e.1, !e.2) :: rest)) by simp]
      simp only [pathHol]
      rw [ih (stepEnd y e) ((e.1, !e.2) :: rest)]
      simp only [pathHol]
      rw [stepHol_flip, stepEnd_flip]
      group

/-- **A closed loop of the form `p ∪ (−p)` has trivial holonomy.** -/
theorem pathHol_loop_invSteps {d : ℕ} (V : LatSite d → Fin d → SU2) (y : LatSite d)
    (p : List (Step d)) : pathHol V y (p ++ invSteps p) = 1 := by
  have h := pathHol_cancel_invSteps V p y []
  rw [List.append_nil] at h
  rw [h]
  rfl

/-! #### §11j — REVERSING THE BLOCK ORDER, at exactly `revCount`

The return staircase traverses the directions in the SAME order as the outbound one (both are
`(List.finRange d).reverse.flatMap`), so the outbound staircase must be re-ordered into the
ascending order before it can cancel against the return. Reversing the order of a list of blocks is
a bubble sort whose cost is the sum of `|block| · |block|` over unordered pairs — `pcL` below — and
that is exactly `revCount`. -/

/-- Pairwise cost of a list of block lengths: `pcL [a₀,…,a_k] = ∑_{i<j} aᵢ·aⱼ`. -/
def pcL : List ℕ → ℕ
  | [] => 0
  | a :: t => a * t.sum + pcL t

theorem pcL_nil : pcL [] = 0 := rfl

theorem pcL_cons (a : ℕ) (t : List ℕ) : pcL (a :: t) = a * t.sum + pcL t := rfl

theorem pcL_append_singleton (l : List ℕ) (a : ℕ) : pcL (l ++ [a]) = pcL l + l.sum * a := by
  induction l with
  | nil => simp [pcL_nil, pcL_cons]
  | cons b t ih =>
      rw [List.cons_append, pcL_cons, ih, pcL_cons, List.sum_append, List.sum_cons]
      simp only [List.sum_nil, List.sum_cons]
      ring

/-- **THE BLOCK REVERSAL.** Reversing the order of a list of blocks of forward steps costs exactly
`∑_{i<j} |bᵢ|·|bⱼ|` conjugated plaquettes — no more, no fewer. -/
theorem deform_blocks_reverse {d : ℕ} (V : LatSite d → Fin d → SU2)
    (g : Fin d → List (Step d)) :
    ∀ ds : List (Fin d), (∀ ρ ∈ ds, ∀ e ∈ g ρ, e.2 = true) →
      Deform V (pcL (ds.map (fun ρ => (g ρ).length))) (ds.reverse.flatMap g) (ds.flatMap g) := by
  intro ds
  induction ds with
  | nil =>
      intro _
      simp only [List.map_nil, List.reverse_nil, List.flatMap_nil, pcL_nil]
      exact Deform.of_eq V rfl
  | cons ρ t ih =>
      intro hfwd
      have hft : ∀ σ ∈ t, ∀ e ∈ g σ, e.2 = true := fun σ hσ => hfwd σ (by simp [hσ])
      have hgρ : ∀ e ∈ g ρ, e.2 = true := hfwd ρ (by simp)
      have hflat : ∀ e ∈ t.flatMap g, e.2 = true := by
        intro e he
        rw [List.mem_flatMap] at he
        obtain ⟨σ, hσ, hmem⟩ := he
        exact hft σ hσ e hmem
      refine (((ih hft).append_right (g ρ)).trans
        (deform_swap V (t.flatMap g) (g ρ) hflat hgρ)).conv ?_ ?_ ?_
      · simp only [List.map_cons, pcL_cons, List.length_flatMap]
        ring
      · simp
      · simp

/-! #### §11k — MOVING THE LEG TO THE FRONT, at exactly `cylCount`

The `μ`-block of the staircase must NOT go through the generic slide (§11c): it would emit `ell·x_μ`
entries whose plaquettes are all trivial, and the total would exceed `surfCount` unrecoverably. The
correct branch is a pure list identity — two runs of the SAME step commute as lists — and it costs
zero, which is why `cylCount`'s sum erases `μ`. -/

theorem coordSteps_natCast {d : ℕ} (ρ : Fin d) (m : ℕ) :
    coordSteps ρ ((m : ℕ) : ℤ) = List.replicate m (ρ, true) := by
  simp only [coordSteps, decide_eq_true (Int.natCast_nonneg m), Int.natAbs_natCast]

theorem coordSteps_natCast_length {d : ℕ} (ρ : Fin d) (m : ℕ) :
    (coordSteps ρ ((m : ℕ) : ℤ)).length = m := by
  rw [coordSteps_natCast, List.length_replicate]

/-- **THE FREE MOVE.** Two coordinate runs in the SAME direction commute as step lists, so nothing
is charged for moving the `μ`-block past the `μ`-leg. -/
theorem coordSteps_swap {d : ℕ} (ρ : Fin d) (m n : ℕ) :
    coordSteps ρ ((m : ℕ) : ℤ) ++ coordSteps ρ ((n : ℕ) : ℤ)
      = coordSteps ρ ((n : ℕ) : ℤ) ++ coordSteps ρ ((m : ℕ) : ℤ) := by
  rw [coordSteps_natCast, coordSteps_natCast, List.replicate_append_replicate,
    List.replicate_append_replicate, Nat.add_comm]

/-- **THE BRANCH POINT OF §11c, AS A SINGLE LEMMA.** One staircase block past the `μ`-leg costs
`ell · x_ρ` if `ρ ≠ μ` and exactly ZERO if `ρ = μ`. -/
theorem deform_block_past_leg {d : ℕ} (V : LatSite d → Fin d → SU2) (μ : Fin d) (ell : ℕ)
    (x : Fin d → ℕ) (ρ : Fin d) :
    Deform V (ell * (if ρ = μ then 0 else x ρ))
      (coordSteps ρ ((x ρ : ℕ) : ℤ) ++ coordSteps μ ((ell : ℕ) : ℤ))
      (coordSteps μ ((ell : ℕ) : ℤ) ++ coordSteps ρ ((x ρ : ℕ) : ℤ)) := by
  by_cases hρ : ρ = μ
  · rw [if_pos hρ, Nat.mul_zero]
    refine Deform.of_eq V ?_
    rw [hρ]
    exact coordSteps_swap μ (x μ) ell
  · rw [if_neg hρ]
    have h := deform_leg V μ ell (coordSteps ρ ((x ρ : ℕ) : ℤ))
      (coordSteps_forward ρ (Int.natCast_nonneg (x ρ)))
    rwa [coordSteps_natCast_length ρ (x ρ)] at h

/-- **THE LEG MOVES TO THE FRONT** at `ell` per NON-`μ` staircase step. -/
theorem deform_leg_to_front {d : ℕ} (V : LatSite d → Fin d → SU2) (μ : Fin d) (ell : ℕ)
    (x : Fin d → ℕ) :
    ∀ ds : List (Fin d),
      Deform V (ell * (ds.map (fun ρ => if ρ = μ then 0 else x ρ)).sum)
        (ds.flatMap (fun σ => coordSteps σ ((x σ : ℕ) : ℤ)) ++ coordSteps μ ((ell : ℕ) : ℤ))
        (coordSteps μ ((ell : ℕ) : ℤ) ++ ds.flatMap (fun σ => coordSteps σ ((x σ : ℕ) : ℤ))) := by
  intro ds
  induction ds with
  | nil =>
      simp only [List.map_nil, List.sum_nil, mul_zero, List.flatMap_nil,
        List.nil_append, List.append_nil]
      exact Deform.of_eq V rfl
  | cons ρ t ih =>
      have mid : Deform V (ell * (t.map (fun σ => if σ = μ then 0 else x σ)).sum)
          (coordSteps ρ ((x ρ : ℕ) : ℤ)
            ++ (t.flatMap (fun σ => coordSteps σ ((x σ : ℕ) : ℤ)) ++ coordSteps μ ((ell : ℕ) : ℤ)))
          ((coordSteps ρ ((x ρ : ℕ) : ℤ) ++ coordSteps μ ((ell : ℕ) : ℤ))
            ++ t.flatMap (fun σ => coordSteps σ ((x σ : ℕ) : ℤ))) :=
        (ih.append_left (coordSteps ρ ((x ρ : ℕ) : ℤ))).conv rfl rfl
          (by simp only [List.append_assoc])
      refine (mid.trans ((deform_block_past_leg V μ ell x ρ).append_right
        (t.flatMap (fun σ => coordSteps σ ((x σ : ℕ) : ℤ))))).conv ?_ ?_ ?_
      · simp only [List.map_cons, List.sum_cons]
        ring
      · simp only [List.flatMap_cons, List.append_assoc]
      · simp only [List.flatMap_cons, List.append_assoc]

/-! #### §11l — THE TWO COUNTS, matched to `cylCount` and `revCount` EXACTLY

The deformations above produce list-recursive counts; `surfCount` is a `Finset` double sum. These
are the bridges, and they are where an off-by-one would show up. -/

/-- The `ℕ`-indexed extension of a `Fin d`-indexed weight — used only to travel between
`List.finRange` and `List.range`. -/
def natExt {d : ℕ} (w : Fin d → ℕ) (n : ℕ) : ℕ := if h : n < d then w ⟨n, h⟩ else 0

theorem natExt_val {d : ℕ} (w : Fin d → ℕ) (ν : Fin d) : natExt w (ν : ℕ) = w ν := by
  simp [natExt]

theorem listSum_range_map (X : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map X).sum = ∑ i ∈ Finset.range n, X i := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

theorem map_finRange_eq_map_range {d : ℕ} (w : Fin d → ℕ) :
    (List.finRange d).map w = (List.range d).map (natExt w) := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left (fun ρ _ => ?_)
  simp [natExt]

theorem finRange_map_sum {d : ℕ} (w : Fin d → ℕ) :
    ((List.finRange d).map w).sum = ∑ ν : Fin d, w ν := by
  rw [map_finRange_eq_map_range, listSum_range_map,
    ← Fin.sum_univ_eq_sum_range (natExt w) d]
  exact Finset.sum_congr rfl (fun ν _ => natExt_val w ν)

theorem pcL_range_map (X : ℕ → ℕ) (n : ℕ) :
    pcL ((List.range n).map X) = ∑ ν ∈ Finset.range n, (∑ ρ ∈ Finset.range ν, X ρ) * X ν := by
  induction n with
  | zero => simp [pcL_nil]
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, pcL_append_singleton,
        ih, listSum_range_map, Finset.sum_range_succ]

/-- **THE REVERSAL COUNT IS `revCount`.** -/
theorem pcL_finRange_eq_revCount {d : ℕ} (w : Fin d → ℕ) :
    pcL ((List.finRange d).map w) = revCount w := by
  rw [map_finRange_eq_map_range, pcL_range_map, revCount,
    ← Fin.sum_univ_eq_sum_range (fun n => (∑ ρ ∈ Finset.range n, natExt w ρ) * natExt w n) d]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  have hset : (∑ ρ ∈ Finset.range (ν : ℕ), natExt w ρ) = ∑ ρ ∈ Finset.Iio ν, w ρ := by
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
    exact Finset.sum_congr rfl (fun ρ _ => by simpa using natExt_val w ρ)
  rw [hset, natExt_val w ν, Finset.sum_mul]

/-- **THE CYLINDER COUNT IS `cylCount`.** The `μ`-term is zero on the left because the `μ`-block
moves for free, and absent on the right because `cylCount`'s sum erases `μ`. Same number. -/
theorem cyl_sum_eq_cylCount {d : ℕ} (ell : ℕ) (x : Fin d → ℕ) (μ : Fin d) :
    ell * (((List.finRange d).map (fun ρ => if ρ = μ then 0 else x ρ)).sum) = cylCount ell x μ := by
  classical
  rw [finRange_map_sum, cylCount]
  congr 1
  have h1 : ∑ ν ∈ Finset.univ.erase μ, (if ν = μ then 0 else x ν)
      = ∑ ν ∈ Finset.univ.erase μ, x ν :=
    Finset.sum_congr rfl (fun ν hν => if_neg (Finset.ne_of_mem_erase hν))
  have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
    (fun ν => if ν = μ then 0 else x ν) (Finset.mem_univ μ)
  rw [if_pos rfl, add_zero] at h2
  rw [← h2, h1]

/-! #### §11m — THE THREE SEGMENTS, IDENTIFIED

The one geometric input the assembly needs beyond the algebra above. The return staircase is NOT the
path-reverse of the outbound one — `stairSteps` fixes its direction order, so both traverse the legs
in the same order — but it IS the path-reverse of the ASCENDING staircase, and together with the
closing leg it is `invSteps (leg ++ ascending)`. Both facts come straight from the extents, and the
`μ`-extent is the one that has to be checked separately. -/

theorem flatMap_funext {α β : Type*} (l : List α) (f g : α → List β) (h : ∀ a, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => simp
  | cons a t ih => simp [h a, ih]

theorem invSteps_coordSteps {d : ℕ} (ρ : Fin d) (n : ℤ) :
    invSteps (coordSteps ρ n) = coordSteps ρ (-n) := by
  rcases eq_or_ne n 0 with h | h
  · subst h; simp [invSteps, coordSteps]
  · have hb : (!decide ((0 : ℤ) ≤ n)) = decide ((0 : ℤ) ≤ -n) := by
      rcases lt_or_gt_of_ne h with hn | hn
      · rw [decide_eq_false (by omega : ¬ (0 : ℤ) ≤ n),
          decide_eq_true (by omega : (0 : ℤ) ≤ -n)]
        rfl
      · rw [decide_eq_true (by omega : (0 : ℤ) ≤ n),
          decide_eq_false (by omega : ¬ (0 : ℤ) ≤ -n)]
        rfl
    simp only [invSteps, coordSteps, List.reverse_replicate, List.map_replicate, hb,
      Int.natAbs_neg]

theorem invSteps_flatMap {d : ℕ} (g : Fin d → List (Step d)) (l : List (Fin d)) :
    invSteps (l.flatMap g) = l.reverse.flatMap (fun ρ => invSteps (g ρ)) := by
  induction l with
  | nil => simp [invSteps]
  | cons a t ih => simp [invSteps_append, ih]

/-- The OUTBOUND staircase from the origin: descending direction order, every step forward. -/
theorem stairSteps_out {d : ℕ} (x : Fin d → ℕ) :
    stairSteps (0 : LatSite d) (fun ρ => (x ρ : ℤ))
      = (List.finRange d).reverse.flatMap (fun ρ => coordSteps ρ ((x ρ : ℕ) : ℤ)) := by
  rw [stairSteps]
  refine flatMap_funext _ _ _ (fun ρ => ?_)
  simp

/-- **THE RETURN STAIRCASE IS THE PATH-REVERSE OF THE *ASCENDING* STAIRCASE.** Every extent is
`−x_ρ`, including at `ρ = μ`, where the two `ell`s cancel: `ell − (x_μ + ell) = −x_μ`. This is the
fact that turns the whole residual into one deformation plus one cancellation. -/
theorem stairSteps_return {d : ℕ} (ell : ℕ) (μ : Fin d) (x : Fin d → ℕ) :
    stairSteps (shiftS (fun ρ => (x ρ : ℤ)) μ ((ell : ℕ) : ℤ))
        (shiftS (0 : LatSite d) μ ((ell : ℕ) : ℤ))
      = invSteps ((List.finRange d).flatMap (fun ρ => coordSteps ρ ((x ρ : ℕ) : ℤ))) := by
  rw [invSteps_flatMap, stairSteps]
  refine flatMap_funext _ _ _ (fun ρ => ?_)
  rw [invSteps_coordSteps]
  congr 1
  by_cases hρ : ρ = μ
  · subst hρ
    simp only [shiftS, Function.update_self, Pi.zero_apply]
    omega
  · simp only [shiftS, Function.update_apply, if_neg hρ, Pi.zero_apply]
    omega

/-! #### §11n — THE ASSEMBLY -/

/-- **THE RESIDUAL, DISCHARGED.** The loop `Γ_{c,x} ∪ (−c)` has a spanning surface with exactly
`surfCount ell xn μ` plaquettes OF THE SAME CONFIGURATION `V`.

Everything on the left is DETERMINED by `V`, `ell`, `μ`, `x`; the only existential is the surface.
§6 derives the count from the p.19 definition of `Γ_{c,x}`; §9 proves that any such product obeys
`‖· − 1‖ ≤ (count)·β`. The proof:

* the loop is `(D ++ L) ++ invSteps (L ++ A)` where `D`/`A` are the descending/ascending staircases
  and `L` the `μ`-leg (`stairSteps_out`, `stairSteps_return`, `invSteps_append`);
* `D ++ L ⟶ A ++ L` by reversing the block order — `revCount xn` plaquettes,
  `deform_blocks_reverse` composed with `pcL_finRange_eq_revCount`;
* `A ++ L ⟶ L ++ A` by moving the leg to the front — `cylCount ell xn μ` plaquettes,
  `deform_leg_to_front` composed with `cyl_sum_eq_cylCount`, the `μ`-block moving for FREE;
* `pathHol V 0 ((L ++ A) ++ invSteps (L ++ A)) = 1` by `pathHol_loop_invSteps`, which is what leaves
  the bare surface product on the right.

The count is `revCount + cylCount = surfCount`, exactly, with no padding and no slack.

The hypothesis `hxn : ∀ ρ, xn ρ ≤ ell − 1` is NOT used: the identity holds for every `xn`. It is
`surfCount_le` that needs smallness, to bound the count by `plaqCount d ell`. -/
theorem loop_is_conj_plaquette_product {d : ℕ} (ell : ℕ) (V : LatSite d → Fin d → SU2)
    (μ : Fin d) (xn : Fin d → ℕ) (hxn : ∀ ρ, xn ρ ≤ ell - 1) :
    ∃ ps : List (SU2 × (LatSite d × Fin d × Fin d)),
      ps.length = surfCount ell xn μ ∧
      pathHol V 0 (gammaLoopSteps ell μ (fun ρ => (xn ρ : ℤ)))
        = (ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹)).prod := by
  classical
  have hloop : gammaLoopSteps ell μ (fun ρ => (xn ρ : ℤ))
      = (((List.finRange d).reverse.flatMap (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ)))
            ++ coordSteps μ ((ell : ℕ) : ℤ))
          ++ invSteps (coordSteps μ ((ell : ℕ) : ℤ)
              ++ (List.finRange d).flatMap (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ))) := by
    rw [gammaLoopSteps, gammaSteps, stairSteps_out, stairSteps_return, invSteps_append]
    simp only [List.append_assoc]
  have hfwd : ∀ ρ ∈ List.finRange d, ∀ e ∈ coordSteps ρ ((xn ρ : ℕ) : ℤ), e.2 = true :=
    fun ρ _ => coordSteps_forward ρ (Int.natCast_nonneg (xn ρ))
  have hg : (fun ρ : Fin d => (coordSteps ρ ((xn ρ : ℕ) : ℤ)).length) = xn :=
    funext (fun ρ => coordSteps_natCast_length ρ (xn ρ))
  have hrev : Deform V (revCount xn)
      ((List.finRange d).reverse.flatMap (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ)))
      ((List.finRange d).flatMap (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ))) := by
    refine (deform_blocks_reverse V (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ))
      (List.finRange d) hfwd).conv ?_ rfl rfl
    rw [hg]
    exact pcL_finRange_eq_revCount xn
  have hcyl : Deform V (cylCount ell xn μ)
      ((List.finRange d).flatMap (fun σ => coordSteps σ ((xn σ : ℕ) : ℤ))
        ++ coordSteps μ ((ell : ℕ) : ℤ))
      (coordSteps μ ((ell : ℕ) : ℤ)
        ++ (List.finRange d).flatMap (fun σ => coordSteps σ ((xn σ : ℕ) : ℤ))) :=
    (deform_leg_to_front V μ ell xn (List.finRange d)).conv
      (cyl_sum_eq_cylCount ell xn μ) rfl rfl
  have hdef : Deform V (surfCount ell xn μ)
      (((List.finRange d).reverse.flatMap (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ)))
        ++ coordSteps μ ((ell : ℕ) : ℤ))
      (coordSteps μ ((ell : ℕ) : ℤ)
        ++ (List.finRange d).flatMap (fun σ => coordSteps σ ((xn σ : ℕ) : ℤ))) :=
    ((hrev.append_right (coordSteps μ ((ell : ℕ) : ℤ))).trans hcyl).conv
      (by rw [surfCount]; exact Nat.add_comm _ _) rfl rfl
  obtain ⟨ps, hlen, hps⟩ := hdef 0 (invSteps (coordSteps μ ((ell : ℕ) : ℤ)
      ++ (List.finRange d).flatMap (fun ρ => coordSteps ρ ((xn ρ : ℕ) : ℤ))))
  refine ⟨ps, hlen, ?_⟩
  rw [hloop, hps, pathHol_loop_invSteps, mul_one]
  rfl

/-! #### §11o — §11 MEETS §9: S5 FOR AN ACTUAL CONFIGURATION, NOT AN ABSTRACT SURFACE

With the surface built, §9's algebraic half no longer needs a spanning surface as a HYPOTHESIS. This
is the composition `loop_is_conj_plaquette_product` → `loop_bound_of_surface`, and it is the first
statement in this file in which S5 is a theorem about a lattice CONFIGURATION rather than a
hypothesis about an abstract `loopHol`/`plaqAt`. Landing it is what keeps §11 off the island. -/

/-- **S5, FOR A CONFIGURATION.** If every plaquette of `V` is within `beta` of `1`, the loop
`Γ_{c,x} ∪ (−c)` of the SAME `V` is within `N(d,L)·beta` of `1`.

Two limitations, disclosed, neither a regression:

* the curvature hypothesis is GLOBAL (`∀ y ρ ν`), where CMP98 p.24 needs it only on the box
  `B(c₋) ∪ B(c₊)`. A global hypothesis makes this theorem WEAKER than the source's, not stronger.
  Localising it needs one named thing: **a site-support invariant on `Deform`** — the slide lemmas
  of §11b–§11f say nothing about WHERE the plaquettes they emit sit, so they would each have to be
  re-proved carrying "every emitted plaquette site lies in the box". The residual's own statement
  never had a locality conjunct either (§11's prose asserted locality; the `Prop` did not), so this
  is a pre-existing gap now named precisely rather than a new one.
* `link_recursion_of_curvature` still takes S5 in its abstract `loopHol` form. Plugging this in
  would change a statement that other modules consume, which is outside this lane's write scope. -/
theorem loop_bound_of_config {d : ℕ} (ell : ℕ) (V : LatSite d → Fin d → SU2) (μ : Fin d)
    (xn : Fin d → ℕ) (hxn : ∀ ρ, xn ρ ≤ ell - 1) (beta : ℝ) (hb : 0 ≤ beta)
    (hplaq : ∀ (y : LatSite d) (ρ ν : Fin d), frobNorm ((plaqHol V y ρ ν : M2) - 1) ≤ beta) :
    frobNorm (((pathHol V 0 (gammaLoopSteps ell μ (fun ρ => (xn ρ : ℤ))) : SU2) : M2) - 1)
      ≤ (plaqCount d ell : ℝ) * beta := by
  obtain ⟨ps, hlen, hps⟩ := loop_is_conj_plaquette_product ell V μ xn hxn
  have hmap : (ps.map (fun q => (q.1, plaqHol V q.2.1 q.2.2.1 q.2.2.2))).map
        (fun q : SU2 × SU2 => (q.1 * q.2 * q.1⁻¹ : SU2))
      = ps.map (fun q => q.1 * plaqHol V q.2.1 q.2.2.1 q.2.2.2 * q.1⁻¹) := by
    simp [List.map_map, Function.comp_def]
  have hbnd : ∀ q ∈ ps.map (fun q => (q.1, plaqHol V q.2.1 q.2.2.1 q.2.2.2)),
      frobNorm ((q.2 : M2) - 1) ≤ beta := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, _, rfl⟩ := hq
    exact hplaq r.2.1 r.2.2.1 r.2.2.2
  have hlen2 : (ps.map (fun q => (q.1, plaqHol V q.2.1 q.2.2.1 q.2.2.2))).length
      = surfCount ell xn μ := by rw [List.length_map, hlen]
  have hbound := loop_bound_of_surface ell xn μ hxn
    (ps.map (fun q => (q.1, plaqHol V q.2.1 q.2.2.1 q.2.2.2))) beta hb hlen2 hbnd
  rw [hmap] at hbound
  rw [hps]
  exact hbound

/-- **THE LINK RECURSION WITH S5 DISCHARGED, NOT ASSUMED.** `link_recursion_of_curvature` takes S5
as the hypothesis `hloop : ‖W l x − 1‖ ≤ N(d,L)·β l` about an abstract family `W`. Here that family
is the ACTUAL loop holonomy of the level-`l` configuration, `W l x = pathHol (V l) 0 Γ_{c,x}`, and
`hloop` is DERIVED from `loop_bound_of_config`. The hypothesis that replaces it is a bound on the
CURVATURE of the configuration, which is the honest input Balaban assumes.

So the recursion `ε(l+1) ≤ L·ε(l) + Kb(d,L)·β(l)` now holds with:

* no abstract `loopHol` and no abstract surface anywhere in the hypotheses;
* one `Kb = (π/2)·N(d,L)`, level-independent, visible in the type;
* `hblk` the block condition `x ρ ≤ L − 1`, which is what `surfCount_le` consumes.

What is still HYPOTHESIS and is NOT S5: `hUc` (the coarse bond is `L` fine bonds — S2, still stated
abstractly), `hnext` (the definition of `ε(l+1)`), `hsmall` (§8's non-antipodal input condition),
and `hcurv`, which is GLOBAL in the site where the source needs it only on `B(c₋) ∪ B(c₊)` — see
`loop_bound_of_config` for the named missing piece (a site-support invariant on `Deform`). -/
theorem link_recursion_of_config
    (d ell k : ℕ) (μ : Fin d) (eps beta : ℕ → ℝ)
    (V : ℕ → LatSite d → Fin d → SU2) (w : ℕ → (Fin d → ℕ) → ℝ) (Uc : ℕ → SU2)
    (blk : Finset (Fin d → ℕ)) (hblk : ∀ x ∈ blk, ∀ ρ, x ρ ≤ ell - 1)
    (hw : ∀ l, ∀ x ∈ blk, 0 ≤ w l x) (hsum : ∀ l, ∑ x ∈ blk, w l x = 1)
    (hUc : ∀ l, l < k → frobNorm ((Uc l : M2) - 1) ≤ (ell : ℝ) * eps l)
    (hbeta : ∀ l, l < k → 0 ≤ beta l)
    (hcurv : ∀ l, l < k → ∀ (y : LatSite d) (ρ ν : Fin d),
        frobNorm ((plaqHol (V l) y ρ ν : M2) - 1) ≤ beta l)
    (hsmall : ∀ l, l < k → (plaqCount d ell : ℝ) * beta l < 2 * Real.sqrt 2)
    (hnext : ∀ l, l < k → eps (l + 1) ≤ frobNorm ((blockedLink blk (w l)
        (fun x => pathHol (V l) 0 (gammaLoopSteps ell μ (fun ρ => (x ρ : ℤ)))) (Uc l) : M2) - 1)) :
    ∀ l, l < k → eps (l + 1) ≤ (ell : ℝ) * eps l + KbConst d ell * beta l := by
  refine link_recursion_of_curvature d ell k eps beta (fun _ => blk) w
    (fun l x => pathHol (V l) 0 (gammaLoopSteps ell μ (fun ρ => (x ρ : ℤ)))) Uc
    (fun l => hw l) (fun l => hsum l) hUc ?_ hsmall hnext
  intro l hl x hx
  exact loop_bound_of_config ell (V l) μ x (hblk x hx) (beta l) (hbeta l hl) (hcurv l hl)

/-! #### §11p — S91: THE STATEMENT IS NOT ABOUT THE TRIVIAL ELEMENT

The degenerate-inhabitation attack on `loop_is_conj_plaquette_product` has exactly two moves, and
this subsection runs both rather than asserting they fail.

1. **Pad the list.** `mu_slide_entries_are_trivial` shows a diagonal entry `(g, (y, ρ, ρ))`
   contributes `1`, so a surface list can always be padded UPWARD for free:
   `∃ ps, ps.length = N ∧ …` is equivalent to `∃ ps, ps.length ≤ N ∧ …`. This attack
   **partially succeeds** and is disclosed in
   §11c — the exact-length conjunct is not the strong constraint that comment originally claimed.
   It does not make the statement vacuous, because a list cannot be SHORTENED.
2. **Make the target trivial.** If `pathHol V 0 (gammaLoopSteps …)` were `1` for every `V`, then the
   all-diagonal list of length `surfCount` would always work and the theorem would assert nothing.
   This attack **FAILS**, and the witness below is why: an explicit configuration on `ℤ²` whose
   `Γ`-loop holonomy is a prescribed `g`. Instantiated at `g = torus (1/2)`, which
   `smallness_class_nontrivial` shows is `≠ 1`, the loop holonomy is nontrivial — so the list the
   theorem produces has a nontrivial ordered product and cannot be the padding list.

Note the parameters: `d = 2`, `ell = 2`, `x ≡ 1`, which **satisfies `x ρ ≤ ell − 1`**, so the
witness lands inside the hypothesis class the theorem is about, not outside it. -/

/-- The witness field: `g` on the `σ = 1` links whose first coordinate is `0`, and `1` elsewhere.
Not flat, and site-dependent in exactly one coordinate so that the evaluation is finite. -/
def wV (g : SU2) (z : LatSite 2) (σ : Fin 2) : SU2 :=
  if σ = 1 ∧ z 0 = 0 then g else 1

/-- The eight steps of the `d = 2, ell = 2, x ≡ 1` loop, by evaluation. -/
theorem wLoop_steps :
    gammaLoopSteps 2 (0 : Fin 2) (fun _ => ((1 : ℕ) : ℤ))
      = [((1 : Fin 2), true), ((0 : Fin 2), true), ((0 : Fin 2), true),
         ((0 : Fin 2), true), ((1 : Fin 2), false), ((0 : Fin 2), false),
         ((0 : Fin 2), false), ((0 : Fin 2), false)] := by
  decide

/-- **THE LOOP HOLONOMY OF THE WITNESS IS `g`.** Only two of the eight steps see a `σ = 1` link, and
of those only the first sits at first coordinate `0`; the closing `σ = 1` step sits at coordinate
`3`. So the eight factors collapse to `g`. -/
theorem wLoop_holonomy (g : SU2) :
    pathHol (wV g) 0 (gammaLoopSteps 2 (0 : Fin 2) (fun _ => ((1 : ℕ) : ℤ))) = g := by
  rw [wLoop_steps]
  simp [pathHol, stepHol, stepEnd, wV, shiftS]

/-- **THE S91 ATTACK FAILS: the residual's target is a nontrivial group element.** -/
theorem wLoop_holonomy_ne_one :
    pathHol (wV (torus (1 / 2))) 0 (gammaLoopSteps 2 (0 : Fin 2) (fun _ => ((1 : ℕ) : ℤ)))
      ≠ 1 := by
  rw [wLoop_holonomy]
  intro h
  have hpos := smallness_class_nontrivial.1
  rw [h] at hpos
  rw [OneMemClass.coe_one, sub_self] at hpos
  exact absurd frobNorm_zero (ne_of_gt hpos)

/-- **AND THE SURFACE IT DEMANDS IS NONEMPTY.** At these parameters the count is `3`, so the theorem
is not satisfied by the empty list either: `surfCount 2 (fun _ => 1) 0 = 2·1 + 1 = 3`. -/
theorem wLoop_surfCount : surfCount 2 (fun _ => 1) (0 : Fin 2) = 3 := by
  decide

/-! ##### §11p (cont.) — and the RECURSION's hypotheses are not degenerate either

`link_recursion_of_config` is a `∀`-implication, so S91's `∃`-attack does not apply to it; the
corresponding hazard is that only DEGENERATE configurations satisfy its hypotheses (the defect that
inhabited `FULL3DTarget` twice). The hypothesis at risk is `hcurv` together with `hsmall`: if small
curvature forced trivial loop holonomy, the recursion would be about nothing.

It does not. The witness field's curvature is bounded by `‖g − 1‖` — every plaquette of `wV g` is
`1`, `g`, or `g⁻¹`, and inverting is a `frobNorm` isometry — while its loop holonomy is `g`. So at
`g = torus (1/2)` the hypotheses `hcurv` (with `β = ‖g − 1‖`) and `hsmall` BOTH hold and the loop
holonomy is nontrivial, simultaneously. Nothing here is flat and nothing here is trivial. -/

/-- Every plaquette of the witness field is `1`, `g` or `g⁻¹`. Three cases in the first coordinate:
`y 0 = -1` puts the `σ = 1` link at the plaquette's far corner, `y 0 = 0` at its near corner, and
every other `y` sees no nontrivial link at all. -/
theorem wV_plaq_trichotomy (g : SU2) (y : LatSite 2) (ρ ν : Fin 2) :
    plaqHol (wV g) y ρ ν = 1 ∨ plaqHol (wV g) y ρ ν = g ∨ plaqHol (wV g) y ρ ν = g⁻¹ := by
  fin_cases ρ <;> fin_cases ν
  · left; exact plaqHol_self _ _ _
  · by_cases h0 : y 0 = 0
    · right; right
      simp [plaqHol, wV, shiftS, h0]
    · by_cases h1 : y 0 = -1
      · right; left
        simp [plaqHol, wV, shiftS, h1]
      · left
        have h1' : y 0 + 1 ≠ 0 := by omega
        simp [plaqHol, wV, shiftS, h0, h1']
  · by_cases h0 : y 0 = 0
    · right; left
      simp [plaqHol, wV, shiftS, h0]
    · by_cases h1 : y 0 = -1
      · right; right
        simp [plaqHol, wV, shiftS, h1]
      · left
        have h1' : y 0 + 1 ≠ 0 := by omega
        simp [plaqHol, wV, shiftS, h0, h1']
  · left; exact plaqHol_self _ _ _

/-- **THE WITNESS FIELD HAS CURVATURE AT MOST `‖g − 1‖`, UNIFORMLY IN THE SITE.** -/
theorem wV_curvature_le (g : SU2) (y : LatSite 2) (ρ ν : Fin 2) :
    frobNorm ((plaqHol (wV g) y ρ ν : M2) - 1) ≤ frobNorm ((g : M2) - 1) := by
  rcases wV_plaq_trichotomy g y ρ ν with h | h | h
  · rw [h, OneMemClass.coe_one, sub_self, frobNorm_zero]
    exact frobNorm_nonneg _
  · rw [h]
  · rw [h, AdalyFormal.Balaban.RegularUQChain.frobNorm_su_inv_sub_one]

/-- **AND THAT CURVATURE IS INSIDE §8's NON-ANTIPODAL WINDOW.** `plaqCount 2 2 = 3` and
`‖torus (1/2) − 1‖ = 2√2·sin(1/4)`, so `3·β = 6√2·sin(1/4) ≤ 6√2/4 < 2√2`. -/
theorem wV_curvature_admits_smallness :
    (plaqCount 2 2 : ℝ) * frobNorm (((torus (1 / 2) : SU2) : M2) - 1) < 2 * Real.sqrt 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hang : su2Angle (torus (1 / 2)) = 1 / 2 := su2Angle_torus (by norm_num) (by linarith)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hval : frobNorm (((torus (1 / 2) : SU2) : M2) - 1) = 2 * Real.sqrt 2 * Real.sin (1 / 4) := by
    rw [frobNorm_sub_one_eq, hang]
    norm_num
  have hsin : Real.sin (1 / 4 : ℝ) ≤ 1 / 4 := Real.sin_le (by norm_num)
  have hsinpos : 0 < Real.sin (1 / 4 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  have hpcn : plaqCount 2 2 = 3 := by decide
  rw [hpcn, hval]
  push_cast
  nlinarith

/-- **THE HYPOTHESES OF `link_recursion_of_config` ARE JOINTLY SATISFIABLE BY A CONFIGURATION WITH
NONTRIVIAL LOOP HOLONOMY.** Small curvature does NOT force a trivial loop here: with
`β = ‖torus (1/2) − 1‖`, `hcurv` holds (`wV_curvature_le`), `hsmall` holds
(`wV_curvature_admits_smallness`), and the loop holonomy is `torus (1/2) ≠ 1`. So the recursion is
not a statement about flat fields. -/
theorem wV_recursion_hypotheses_nondegenerate :
    (∀ (y : LatSite 2) (ρ ν : Fin 2),
        frobNorm ((plaqHol (wV (torus (1 / 2))) y ρ ν : M2) - 1)
          ≤ frobNorm (((torus (1 / 2) : SU2) : M2) - 1))
      ∧ (plaqCount 2 2 : ℝ) * frobNorm (((torus (1 / 2) : SU2) : M2) - 1) < 2 * Real.sqrt 2
      ∧ pathHol (wV (torus (1 / 2))) 0 (gammaLoopSteps 2 (0 : Fin 2) (fun _ => ((1 : ℕ) : ℤ)))
          ≠ 1 :=
  ⟨wV_curvature_le (torus (1 / 2)), wV_curvature_admits_smallness, wLoop_holonomy_ne_one⟩

end Residual

/-! ### §11b — the downstream number

`GammaLevelDefect`'s bar is `d·[(d−1) + 2Kb/(ell(ell−1))]·α₀ < 1` (its `Ecst` is
`(d−1)α₀ + 2Kb·α₀/(ell(ell−1))`, increasing in `Kb` for `α₀ ≥ 0`). At `d = 3, ell = 2` the bracket
is `3·[2 + Kb]`. The ASSUMED `Kb = 12` makes it `42`, i.e. the threshold `α₀ < 1/42`. The DERIVED
`Kb = 7π/2` makes it `< 39`, i.e. `α₀ < 1/39` — a strictly WIDER admissible class. Deriving the
constant therefore does not cost anything downstream; it buys. (Stated here without importing
`GammaLevelDefect`, which a concurrent lane owns; the arithmetic is self-contained.) -/
theorem derived_Kb_widens_threshold :
    3 * (2 + KbConst 3 2) < 39 ∧ 3 * (2 + (12 : ℝ)) = 42 := by
  refine ⟨?_, by norm_num⟩
  rw [KbConst, plaqCount_3_2]
  have hp : Real.pi < 3.1416 := Real.pi_lt_d4
  push_cast
  linarith

/-- **AND AT `ell = 3` THE ASSUMED `Kb = 12` IS *NOT* CONSERVATIVE — it is optimistic.**
`GammaLevelDefect.threshold_d3_ell3_Kb12` reads "`d = 3, ell = 3, Kb = 12`: the bar holds **iff**
`α₀ < 1/18`". At `d = 3, ell = 3` the bracket is `3·[2 + 2Kb/6] = 6 + Kb`, so `Kb = 12` gives `18`.
But the DERIVED constant is `KbConst 3 3 = 12π ≈ 37.70`, over three times larger, and the bracket
becomes `6 + 12π > 43`. **The honest `ell = 3` threshold is `α₀ < 1/43.7`, not `1/18`** — a
`2.4×` tightening of a number already in the tree.

The route's stated ceiling is untouched: with `Kb ≥ 0` the bracket is always `≥ d(d−1) = 6`, so
`α₀ < 1/6` remains the `d = 3` ceiling.

So the effect of deriving `Kb` is NOT uniformly favourable: it widens the class at `ell = 2` and
narrows it at `ell = 3`. Reported as a fact; the significance is not this module's to rule on. -/
theorem derived_Kb_3_3_exceeds_twelve :
    (12 : ℝ) < KbConst 3 3 ∧ (43 : ℝ) < 6 + KbConst 3 3 ∧ (6 : ℝ) + 12 = 18 := by
  have hlo : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  refine ⟨?_, ?_, by norm_num⟩ <;> · rw [KbConst, plaqCount_3_3]; push_cast; linarith

/-! ## §12 — AXIOM AUDIT -/

#print axioms frobNorm_su2Log_le_pi_div_two
#print axioms frobNorm_sub_one_le_frobNorm_su2Log
#print axioms frobNorm_sub_one_eq
#print axioms frobNorm_blockExponent_le
#print axioms frobNorm_su2Exp_sub_one_le
#print axioms blockedLink_sub_one_le
#print axioms surfCount_le
#print axioms plaqCount_3_2
#print axioms KbConst_3_2_lt_twelve
#print axioms gammaPathLength_le
#print axioms lassoCount_dir_one
#print axioms link_recursion_of_blocking
#print axioms diag_eq
#print axioms su2Log_su2Exp_of_lt_pi
#print axioms branch_of_frobNorm_lt
#print axioms blockedLink_sub_one_le_of_curvature
#print axioms link_recursion_of_curvature
#print axioms frobNorm_conj_sub_one
#print axioms straight_bond_bound
#print axioms frobNorm_conjProd_sub_one_le
#print axioms loop_bound_of_surface
#print axioms smallness_class_nontrivial
#print axioms derived_Kb_widens_threshold
#print axioms derived_Kb_3_3_exceeds_twelve
#print axioms pathHol_append
#print axioms pathHol_cancel_invSteps
#print axioms pathHol_loop_invSteps
#print axioms deform_swap
#print axioms deform_leg
#print axioms deform_blocks_reverse
#print axioms deform_block_past_leg
#print axioms deform_leg_to_front
#print axioms pcL_finRange_eq_revCount
#print axioms cyl_sum_eq_cylCount
#print axioms invSteps_coordSteps
#print axioms stairSteps_out
#print axioms stairSteps_return
#print axioms loop_is_conj_plaquette_product
#print axioms loop_bound_of_config
#print axioms link_recursion_of_config
#print axioms wLoop_steps
#print axioms wLoop_holonomy
#print axioms wLoop_holonomy_ne_one
#print axioms wLoop_surfCount
#print axioms wV_plaq_trichotomy
#print axioms wV_curvature_le
#print axioms wV_curvature_admits_smallness
#print axioms wV_recursion_hypotheses_nondegenerate

end AdalyFormal.Balaban.BlockingLinkEstimate
