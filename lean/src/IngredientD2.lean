import AdalyFormal.Balaban.SourceJ
import Mathlib

/-!
# IngredientD2 -- `D̃⁽²⁾` of CMP99b (3.155) from its printed (indirect) definition

NOT printed in CMP99b: p.427 says only "a quadratic polynomial in B with properties similar to
C⁽²⁾(A), only restricted to unit blocks".  The definition is printed in the later papers:
 * CMP102-UV pp.259-260 (14)-(18): `Q(A') = QA' + C(A')`; `Q D̃(A,c) = C(A − D̃(A,c), c)`;
   "We assume that D̃(A,b,c) = 0 for all b ≠ b₀(c)"; `Q D̃⁽²⁾(A,c) = C⁽²⁾(A,c)`.
 * CMP109 p.267: `L Q̃ B' + C̃(B') = L Q̃ B − D̃(B) + C̃(B − h D̃(B)) = L Q̃ B`, `B' = B − hD̃(B)`,
   `L Q̃ h = I`, `hB = 0` off `{b₀(c)}`, `D̃⁽²⁾(B) = C̃⁽²⁾(B)`; identifies the quadratic form with CMP99b (3.156).
 (compute/h_construction/final/source-research/REPORT.md, images CMP102-UV_p259/260, CMP109_p267.)
Unit-bond-valued slot of (3.155): `D̃⁽²⁾_unit = h ∘ C⁽²⁾_raw`, `C⁽²⁾_raw` = second-order Taylor
term of the raw nonlinear average `Qraw` (CMP98 (15),(63),(89); NOT built here).
Here: `D2unit h Qraw := h ∘ Dtilde2Shape Qraw`, with the homogeneity law the `Ingr` structure needs PROVED.
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamily

open AdalyFormal.Balaban.SourceJ (taylorQuadraticTerm Dtilde2Shape)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem taylorQuadraticTerm_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (c : ℝ) :
    taylorQuadraticTerm (fun t => g (c * t)) = c ^ 2 • taylorQuadraticTerm g := by
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => g (c * t)) = fun t => c • deriv g (c * t) := by
    funext t; exact deriv_comp_mul_left c g t
  have h2 : deriv (fun t : ℝ => c • deriv g (c * t)) 0 = c ^ 2 • deriv (deriv g) 0 := by
    have h3 := deriv_const_smul_field (x := (0:ℝ)) c (fun s => deriv g (c * s))
    have h4 := deriv_comp_mul_left c (deriv g) 0
    simp only [Pi.smul_def] at h3
    rw [h3, h4]
    simp [smul_smul, pow_two]
  rw [h1, h2, smul_comm]

/-- Homogeneity of degree 2 (what `Ingr.D2_quad` requires of `D̃⁽²⁾`). -/
theorem Dtilde2Shape_homog (Q : X → Y) (c : ℝ) (B : X) :
    Dtilde2Shape Q (c • B) = c ^ 2 • Dtilde2Shape Q B := by
  unfold Dtilde2Shape
  have : (fun t : ℝ => Q (t • c • B)) = fun t => (fun s : ℝ => Q (s • B)) (c * t) := by
    funext t; simp [smul_smul, mul_comm]
  rw [this]
  exact taylorQuadraticTerm_scale (fun s => Q (s • B)) c

/-- `D̃⁽²⁾_unit(B) = h (C⁽²⁾_raw(B))`. -/
noncomputable def D2unit (h : Y →L[ℝ] X) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Qraw : Z → Y) (B : Z) : X := h (Dtilde2Shape Qraw B)

theorem D2unit_quad (h : Y →L[ℝ] X) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Qraw : Z → Y) (c : ℝ) (B : Z) : D2unit h Qraw (c • B) = c ^ 2 • D2unit h Qraw B := by
  unfold D2unit
  rw [Dtilde2Shape_homog, map_smul]

/-- Linear part drops out: a raw map `LQ B + C(B)` has the same second-order term as `C`
(for rays along which `C` is differentiable). -/
theorem Dtilde2Shape_add_linear (Lq : X →L[ℝ] Y) (C : X → Y) (B : X)
    (hC : Differentiable ℝ (fun s : ℝ => C (s • B))) :
    Dtilde2Shape (fun x => Lq x + C x) B = Dtilde2Shape C B := by
  unfold Dtilde2Shape taylorQuadraticTerm
  have h1 : (fun t : ℝ => Lq (t • B) + C (t • B)) = fun t => t • Lq B + C (t • B) := by
    funext t; simp
  rw [h1]
  have h2 : deriv (fun t : ℝ => t • Lq B + C (t • B)) = fun t => Lq B + deriv (fun s : ℝ => C (s • B)) t := by
    funext t
    have hl : HasDerivAt (fun t : ℝ => t • Lq B) (Lq B) t := by
      simpa using (hasDerivAt_id t).smul_const (Lq B)
    have := (hl.add (hC t).hasDerivAt).deriv
    exact this
  rw [h2, deriv_const_add]

/-- Control (S82): a linear raw map has zero second-order term; the genuinely quadratic map
`x ↦ x*x` has nonzero one (`Dtilde2Shape_sq` in SourceJ). -/
theorem D2unit_linear_zero (Lq : X →L[ℝ] Y) (h : Y →L[ℝ] X) (B : X) :
    D2unit h (fun x => Lq x) B = 0 := by
  have := Dtilde2Shape_add_linear Lq (fun _ => (0 : Y)) B (by simp [differentiable_const])
  unfold D2unit
  have h0 : Dtilde2Shape (fun x => Lq x + (0:Y)) B = Dtilde2Shape (fun _ => (0:Y)) B := this
  have h3 : Dtilde2Shape (fun _ : X => (0 : Y)) B = 0 := by
    unfold Dtilde2Shape taylorQuadraticTerm; simp
  simp only [add_zero] at h0
  rw [h0, h3, map_zero]

#print axioms D2unit_quad
#print axioms Dtilde2Shape_add_linear
#print axioms D2unit_linear_zero

end AdalyFormal.IngredientFamily
