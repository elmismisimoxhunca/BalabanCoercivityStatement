import BalabanCompact.Form
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The operators of CMP99b (3.10), (3.24), (3.119), (3.122), (3.128), (3.157)

Built from `Form.lean`'s jets (`QlinStep`, `C2Step`, `qStep`) and from `deltaPrimeSum` / `plaqIn`.
`Ring.inverse` is `0` off the units, and the corridor lift `h` is `0` when `H₀` is not bijective.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace BalabanCompact

open Matrix Complex ContinuousLinearMap
open scoped Classical RealInnerProductSpace

variable {L : Extent}

abbrev SiteL2 (L : Extent) := PiLp 2 (fun _ : Site L => Vec)

noncomputable instance (L : Extent) : FiniteDimensional ℝ (Field L) := inferInstance
noncomputable instance (L : Extent) : FiniteDimensional ℝ (SiteL2 L) := inferInstance
instance (L : Extent) : CompleteSpace (Field L) := FiniteDimensional.complete ℝ _
instance (L : Extent) : CompleteSpace (SiteL2 L) := FiniteDimensional.complete ℝ _
instance (L : Extent) (S : Submodule ℝ (Field L)) : CompleteSpace S := FiniteDimensional.complete ℝ S
instance (L : Extent) (S : Submodule ℝ (SiteL2 L)) : CompleteSpace S := FiniteDimensional.complete ℝ S

noncomputable section

/-! ## Linearity of the chart -/

lemma toM_add (v w : Vec) : toM (v + w) = toM v + toM w := by
  simp only [toM, PiLp.add_apply, add_smul, Finset.sum_add_distrib]

lemma toM_smul (c : ℝ) (v : Vec) : toM (c • v) = c • toM v := by
  unfold toM
  simp only [PiLp.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul, mul_smul]

lemma fromM_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) : fromM (X + Y) = fromM X + fromM Y := by
  ext i
  fin_cases i <;>
    simp [fromM, Matrix.add_apply, mul_add, Complex.add_re, Complex.add_im]

lemma fromM_smul (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : fromM (c • X) = c • fromM X := by
  ext i
  fin_cases i <;>
    simp [fromM, Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma Rmap_add (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v w : Vec) :
    Rmap U (v + w) = Rmap U v + Rmap U w := by
  simp only [Rmap, toM_add, Matrix.mul_add, Matrix.add_mul, fromM_add]

lemma Rmap_smul (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (c : ℝ) (v : Vec) :
    Rmap U (c • v) = c • Rmap U v := by
  simp only [Rmap, toM_smul, Matrix.mul_smul, Matrix.smul_mul, fromM_smul]

lemma conjM_add (U : Matrix (Fin 2) (Fin 2) ℂ) (v w : Vec) :
    conjM U (v + w) = conjM U v + conjM U w := by
  simp only [conjM, toM_add, Matrix.mul_add, Matrix.add_mul, fromM_add]

lemma conjM_smul (U : Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ) (v : Vec) :
    conjM U (c • v) = c • conjM U v := by
  simp only [conjM, toM_smul, Matrix.mul_smul, Matrix.smul_mul, fromM_smul]

lemma curlM_add (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → Vec) (p : Plaq L) :
    curlM U (fun b => A b + B b) p = curlM U A p + curlM U B p := by
  simp only [curlM, Pi.add_apply, conjM_add]
  abel

lemma curlM_smul (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ) (A : Bond L → Vec) (p : Plaq L) :
    curlM U (fun b => c • A b) p = c • curlM U A p := by
  simp only [curlM, Pi.smul_apply, conjM_smul, smul_sub, smul_add]

lemma ntr_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) : ntr (X + Y) = ntr X + ntr Y := by
  unfold ntr
  simp [Matrix.trace_add, Complex.add_re]
  ring

lemma ntr_smul (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : ntr (c • X) = c * ntr X := by
  unfold ntr
  simp [Matrix.trace_smul, Complex.real_smul]
  ring

lemma D2Step_add_left (s ell : ℕ) (V0 : Cfg L) (a a' b : Bond L → Vec) :
    D2Step s ell V0 (a + a') b = D2Step s ell V0 a b + D2Step s ell V0 a' b := by
  funext c
  simp only [D2Step, Pi.add_apply]
  rw [map_add, _root_.add_apply]

lemma D2Step_add_right (s ell : ℕ) (V0 : Cfg L) (a b b' : Bond L → Vec) :
    D2Step s ell V0 a (b + b') = D2Step s ell V0 a b + D2Step s ell V0 a b' := by
  funext c
  simp only [D2Step, Pi.add_apply, map_add]

lemma D2Step_smul_left (s ell : ℕ) (V0 : Cfg L) (r : ℝ) (a b : Bond L → Vec) :
    D2Step s ell V0 (r • a) b = r • D2Step s ell V0 a b := by
  funext c
  simp only [D2Step, Pi.smul_apply]
  rw [map_smul, _root_.smul_apply]

lemma D2Step_smul_right (s ell : ℕ) (V0 : Cfg L) (r : ℝ) (a b : Bond L → Vec) :
    D2Step s ell V0 a (r • b) = r • D2Step s ell V0 a b := by
  funext c
  simp only [D2Step, Pi.smul_apply, map_smul]

/-! ## A bilinear form determines a symmetric operator -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

noncomputable def bilinOp (β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm
        (LinearMap.toContinuousLinearMap (β.flip y))
      map_add' := fun y z => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext x
        rw [LinearIsometryEquiv.map_add]
        simp only [InnerProductSpace.toDual_apply_apply, _root_.add_apply,
          InnerProductSpace.toDual_symm_apply, LinearMap.flip_apply, map_add]
      map_smul' := fun c y => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext x
        simp only [InnerProductSpace.toDual_apply_apply, inner_smul_left, RingHom.id_apply]
        rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
        simp only [LinearMap.flip_apply, map_smul, _root_.smul_apply, smul_eq_mul, star_trivial,
          starRingEnd_apply] }

theorem inner_bilinOp (β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) : ⟪x, bilinOp β y⟫ = β x y := by
  rw [real_inner_comm]
  simp only [bilinOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [InnerProductSpace.toDual_symm_apply]
  simp [LinearMap.flip_apply]

/-- Symmetrisation of a bilinear form. `⟪x, symmOp β x⟫ = β x x`. -/
noncomputable def symmOp (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →L[ℝ] E :=
  bilinOp ((1 / 2 : ℝ) • (β0 + β0.flip))

theorem inner_symmOp_diag (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) : ⟪x, symmOp β0 x⟫ = β0 x x := by
  unfold symmOp
  rw [inner_bilinOp]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  ring

theorem symmOp_symm (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) : ⟪symmOp β0 x, y⟫ = ⟪x, symmOp β0 y⟫ := by
  unfold symmOp
  rw [real_inner_comm y (bilinOp _ x), inner_bilinOp, inner_bilinOp]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  ring

end

variable {L : Extent}

noncomputable section

/-! ## Carriers between `PiLp` and plain functions -/

def matU (U : Cfg L) : Bond L → Matrix (Fin 2) (Fin 2) ℂ :=
  fun b => (U b : Matrix (Fin 2) (Fin 2) ℂ)

def ofBond : Field L →ₗ[ℝ] (Bond L → Vec) :=
  (WithLp.linearEquiv 2 ℝ (Bond L → Vec)).toLinearMap

def toBond : (Bond L → Vec) →ₗ[ℝ] Field L :=
  (WithLp.linearEquiv 2 ℝ (Bond L → Vec)).symm.toLinearMap

def ofSite : SiteL2 L →ₗ[ℝ] (Site L → Vec) :=
  (WithLp.linearEquiv 2 ℝ (Site L → Vec)).toLinearMap

def toSite : (Site L → Vec) →ₗ[ℝ] SiteL2 L :=
  (WithLp.linearEquiv 2 ℝ (Site L → Vec)).symm.toLinearMap

@[simp] lemma ofBond_apply (A : Field L) : ofBond A = ofField A := rfl
@[simp] lemma toBond_apply (A : Bond L → Vec) : toBond A = toField A := rfl

/-! ## Background tower, CMP98 (43), and `Q'` (3.19) -/

noncomputable def ofMat (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  if h : M ∈ specialUnitaryGroup (Fin 2) ℂ then ⟨M, h⟩ else 1

noncomputable def bgStep (s ell : ℕ) (V : Cfg L) : Cfg L :=
  fun c => ofMat (blocked s ell (matU V) c)

noncomputable def bgTower (ell : ℕ) (U : Cfg L) : ℕ → Cfg L
  | 0 => U
  | l + 1 => bgStep (ell ^ l) ell (bgTower ell U l)

noncomputable def transport (s : ℕ) (V : Cfg L) (y x : Site L) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ofMat (coarseHol s (matU V) y (gammaPath s y x))

/-- `(Q'(V)λ)(y) = ℓ^{-3} ∑_{x ∈ B(y)} R(V(Γ_{y,x})) λ(x)`. -/
noncomputable def stepAvgLM (s ell : ℕ) (V : Cfg L) : (Site L → Vec) →ₗ[ℝ] (Site L → Vec) where
  toFun lam := fun y =>
    ((ell : ℝ) ^ 3)⁻¹ • ∑ x ∈ stepBlock y s ell, Rmap (transport s V y x) (lam x)
  map_add' lam lam' := by
    funext y
    have h : ∀ x, Rmap (transport s V y x) ((lam + lam') x) =
        Rmap (transport s V y x) (lam x) + Rmap (transport s V y x) (lam' x) := by
      intro x; rw [Pi.add_apply, Rmap_add]
    simp_rw [h]
    rw [Finset.sum_add_distrib, smul_add, Pi.add_apply]
  map_smul' c lam := by
    funext y
    have h : ∀ x, Rmap (transport s V y x) ((c • lam) x) =
        c • Rmap (transport s V y x) (lam x) := by
      intro x; rw [Pi.smul_apply, Rmap_smul]
    rw [Pi.smul_apply]
    simp_rw [h, Finset.smul_sum, ← mul_smul, mul_comm, mul_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul, smul_smul, mul_comm]
    simp [RingHom.id_apply]

noncomputable def QcompLM (ell : ℕ) (bg : ℕ → Cfg L) : ℕ → (Site L → Vec) →ₗ[ℝ] (Site L → Vec)
  | 0 => LinearMap.id
  | j + 1 => stepAvgLM (ell ^ j) ell (bg j) ∘ₗ QcompLM ell bg j

noncomputable def Qlev (ell : ℕ) (bg : ℕ → Cfg L) (j : ℕ) (y : Site L) : SiteL2 L →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap ((LinearMap.proj y).comp (QcompLM ell bg j ∘ₗ ofSite))

/-! ## `a_j` of (3.24) and the site mass `Q'*aQ'` -/

noncomputable def aSeqAux (a d : ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => a * aSeqAux a d n / (d + aSeqAux a d n)

/-- `a_0 = a_1 = a`, `a_{j+1} = a a_j / (a ℓ^{-2} + a_j)`. -/
noncomputable def ajSeq (a : ℝ) (ell j : ℕ) : ℝ :=
  if j = 0 then a else aSeqAux a (a / ((ell : ℝ) * (ell : ℝ))) (j - 1)

noncomputable def rankOne (ℓ : SiteL2 L →L[ℝ] Vec) : SiteL2 L →L[ℝ] SiteL2 L :=
  (ContinuousLinearMap.adjoint ℓ).comp ℓ

noncomputable def Qpa (ell k : ℕ) (bg : ℕ → Cfg L) (Lam : ℕ → Set (Site L)) (a : ℝ) :
    SiteL2 L →L[ℝ] SiteL2 L :=
  ∑ j ∈ Finset.range (k + 1), ∑ y : Site L,
    if y ∈ Lam j then (ajSeq a ell j * (ell : ℝ) ^ j) • rankOne (Qlev ell bg j y) else 0

/-! ## Gradient, Dirichlet Laplacian, `G'`, `R` -/

noncomputable def gradPlain (U : Cfg L) : (Site L → Vec) →ₗ[ℝ] (Bond L → Vec) where
  toFun lam := fun b => gradValue U lam b
  map_add' lam lam' := by
    funext b
    simp only [gradValue, Pi.add_apply, Rmap_add]
    abel
  map_smul' c lam := by
    funext b
    simp only [gradValue, Pi.smul_apply, Rmap_smul, smul_sub, RingHom.id_apply]

noncomputable def gradL (U : Cfg L) : SiteL2 L →L[ℝ] Field L :=
  LinearMap.toContinuousLinearMap (toBond ∘ₗ gradPlain U ∘ₗ ofSite)

noncomputable def gradAdj (U : Cfg L) : Field L →L[ℝ] SiteL2 L :=
  ContinuousLinearMap.adjoint (gradL U)

noncomputable def lapFull (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  (gradAdj U).comp (gradL U)

noncomputable def siteMask (S : Set (Site L)) : SiteL2 L →L[ℝ] SiteL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun x => if x ∈ S then (WithLp.ofLp f) x else 0
      map_add' := fun f g => by
        refine PiLp.ext fun x => ?_
        simp only [WithLp.ofLp_toLp, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := fun c f => by
        refine PiLp.ext fun x => ?_
        simp only [WithLp.ofLp_toLp, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

noncomputable def DelpA (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L))
    (Lam : ℕ → Set (Site L)) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  ((siteMask Om0).comp (lapFull U + Qpa ell k bg Lam a)).comp (siteMask Om0)

/-- `G'`, inverse on `L²(Ω₀)`, extended by `0`. -/
noncomputable def Gp (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L))
    (Lam : ℕ → Set (Site L)) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  (Ring.inverse (DelpA ell k bg Om0 Lam U a + (1 - siteMask Om0))).comp (siteMask Om0)

def NQp (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L)) :
    Submodule ℝ (SiteL2 L) where
  carrier := {f | (∀ x, x ∉ Om0 → f x = 0) ∧
    ∀ j, j ≤ k → ∀ y, y ∈ Lam j → Qlev ell bg j y f = 0}
  zero_mem' := ⟨fun _ _ => PiLp.zero_apply _ _, fun _ _ _ _ => map_zero _⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun x hx => by rw [PiLp.add_apply, hf.1 x hx, hg.1 x hx, add_zero],
      fun j hj y hy => by rw [map_add, hf.2 j hj y hy, hg.2 j hj y hy, add_zero]⟩
  smul_mem' := fun c f hf =>
    ⟨fun x hx => by rw [PiLp.smul_apply, hf.1 x hx, smul_zero],
      fun j hj y hy => by rw [map_smul, hf.2 j hj y hy, smul_zero]⟩

noncomputable def lapDir (Om0 : Set (Site L)) (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  ((siteMask Om0).comp (lapFull U)).comp (siteMask Om0)

noncomputable def RImage (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L))
    (Lam : ℕ → Set (Site L)) (U : Cfg L) : Submodule ℝ (SiteL2 L) :=
  Submodule.map (lapDir Om0 U : SiteL2 L →ₗ[ℝ] SiteL2 L) (NQp ell k bg Om0 Lam)

/-- `R`, the orthogonal projection onto `Δ_U N(Q')`. -/
noncomputable def Rproj (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L))
    (Lam : ℕ → Set (Site L)) (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  (RImage ell k bg Om0 Lam U).starProjection

end

end BalabanCompact
