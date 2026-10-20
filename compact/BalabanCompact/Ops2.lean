import BalabanCompact.Ops

/-!
# `Δ`, `G₁⁻¹`, `H₁`, `C` and `genForm`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace BalabanCompact

open Matrix Complex ContinuousLinearMap
open scoped Classical RealInnerProductSpace

variable {L : Extent}

noncomputable section

/-! ## `J` of (3.11), plaquettes in `P`, chart `a = i A` (`fromM (I • J)`) -/

def piProj (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  X - (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

def Fnu (P : Set (Plaq L)) (U : Cfg L) (ν μ : Fin 3) (y : Site L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  if hlt : ν < μ then
    if (y, (⟨(ν, μ), hlt⟩ : PlaqDir)) ∈ P then piProj (imHol U (y, ⟨(ν, μ), hlt⟩)) else 0
  else if hgt : μ < ν then
    if (y, (⟨(μ, ν), hgt⟩ : PlaqDir)) ∈ P then -piProj (imHol U (y, ⟨(μ, ν), hgt⟩)) else 0
  else 0

def dstarDir (U : Cfg L) (ν : Fin 3) (G : Site L → Matrix (Fin 2) (Fin 2) ℂ) (x : Site L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let g := ((U (shiftBack x ν, ν))⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)
  g * G (shiftBack x ν) * g⁻¹ - G x

def Jmat (P : Set (Plaq L)) (U : Cfg L) (x : Site L) (μ : Fin 3) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ ν : Fin 3, if ν = μ then 0 else dstarDir U ν (Fnu P U ν μ) x

def Jvec (P : Set (Plaq L)) (U : Cfg L) (b : Bond L) : Vec :=
  fromM (I • Jmat P U b.1 b.2)

def Jfield (P : Set (Plaq L)) (U : Cfg L) : Field L :=
  toField fun b => Jvec P U b

/-! ## Bilinear `Δ'` and the curl energy, on `plaqIn` -/

def edge1 (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) :
    (Bond L → Vec) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := -(U (p.1, p.2.1.2) * toM (A (shift p.1 p.2.1.2, p.2.1.1)) * (U (p.1, p.2.1.2))ᴴ)
  map_add' A B := by simp only [Pi.add_apply, toM_add, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c A := by
    simp only [Pi.smul_apply, toM_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg, RingHom.id_apply]

def edge2 (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) :
    (Bond L → Vec) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := -toM (A (p.1, p.2.1.2))
  map_add' A B := by simp only [Pi.add_apply, toM_add, neg_add]
  map_smul' c A := by simp only [Pi.smul_apply, toM_smul, smul_neg, RingHom.id_apply]

def edge3 (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) :
    (Bond L → Vec) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := toM (A (p.1, p.2.1.1))
  map_add' A B := by simp only [Pi.add_apply, toM_add]
  map_smul' c A := by simp only [Pi.smul_apply, toM_smul, RingHom.id_apply]

def edge4 (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) :
    (Bond L → Vec) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := U (p.1, p.2.1.1) * toM (A (shift p.1 p.2.1.1, p.2.1.2)) * (U (p.1, p.2.1.1))ᴴ
  map_add' A B := by simp only [Pi.add_apply, toM_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    simp only [Pi.smul_apply, toM_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def curlAt (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) :
    (Bond L → Vec) →ₗ[ℝ] Vec where
  toFun A := curlM U A p
  map_add' A B := curlM_add U A B p
  map_smul' c A := curlM_smul U c A p

def toMLM : Vec →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := toM
  map_add' := toM_add
  map_smul' := toM_smul

def smulILM : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := I • X
  map_add' X Y := smul_add _ X Y
  map_smul' c X := smul_comm I c X

def quadLM (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y => (1 / 2 : ℝ) * (ntr (X * Y * M) + ntr (Y * X * M)))
    (fun X1 X2 Y => by
      have h1 : ntr ((X1 + X2) * Y * M) = ntr (X1 * Y * M) + ntr (X2 * Y * M) := by
        rw [Matrix.add_mul, Matrix.add_mul, ntr_add]
      have h2 : ntr (Y * (X1 + X2) * M) = ntr (Y * X1 * M) + ntr (Y * X2 * M) := by
        rw [Matrix.mul_add, Matrix.add_mul, ntr_add]
      rw [h1, h2]; ring)
    (fun c X Y => by
      have h1 : ntr ((c • X) * Y * M) = c * ntr (X * Y * M) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, ntr_smul]
      have h2 : ntr (Y * (c • X) * M) = c * ntr (Y * X * M) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ntr_smul]
      rw [h1, h2]; ring)
    (fun X Y1 Y2 => by
      have h1 : ntr (X * (Y1 + Y2) * M) = ntr (X * Y1 * M) + ntr (X * Y2 * M) := by
        rw [Matrix.mul_add, Matrix.add_mul, ntr_add]
      have h2 : ntr ((Y1 + Y2) * X * M) = ntr (Y1 * X * M) + ntr (Y2 * X * M) := by
        rw [Matrix.add_mul, Matrix.add_mul, ntr_add]
      rw [h1, h2]; ring)
    (fun c X Y => by
      have h1 : ntr (X * (c • Y) * M) = c * ntr (X * Y * M) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ntr_smul]
      have h2 : ntr ((c • Y) * X * M) = c * ntr (Y * X * M) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, ntr_smul]
      rw [h1, h2]; ring)

def brLM (Im : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y => ntr ((I • Y) * X * Im) - ntr ((I • X) * Y * Im))
    (fun X1 X2 Y => by
      rw [smul_add]
      have h1 : ntr ((I • X1 + I • X2) * Y * Im) =
          ntr ((I • X1) * Y * Im) + ntr ((I • X2) * Y * Im) := by
        rw [Matrix.add_mul, Matrix.add_mul, ntr_add]
      have h2 : ntr ((I • Y) * (X1 + X2) * Im) =
          ntr ((I • Y) * X1 * Im) + ntr ((I • Y) * X2 * Im) := by
        rw [Matrix.mul_add, Matrix.add_mul, ntr_add]
      rw [h1, h2]; ring)
    (fun c X Y => by
      rw [smul_comm I c X]
      have h1 : ntr ((c • (I • X)) * Y * Im) = c * ntr ((I • X) * Y * Im) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, ntr_smul]
      have h2 : ntr ((I • Y) * (c • X) * Im) = c * ntr ((I • Y) * X * Im) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ntr_smul]
      rw [h1, h2]
      ring)
    (fun X Y1 Y2 => by
      have h1 : ntr ((I • X) * (Y1 + Y2) * Im) =
          ntr ((I • X) * Y1 * Im) + ntr ((I • X) * Y2 * Im) := by
        rw [Matrix.mul_add, Matrix.add_mul, ntr_add]
      rw [smul_add]
      have h2 : ntr ((I • Y1 + I • Y2) * X * Im) =
          ntr ((I • Y1) * X * Im) + ntr ((I • Y2) * X * Im) := by
        rw [Matrix.add_mul, Matrix.add_mul, ntr_add]
      rw [h1, h2]; ring)
    (fun c X Y => by
      rw [smul_comm I c Y]
      have h1 : ntr ((I • X) * (c • Y) * Im) = c * ntr ((I • X) * Y * Im) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ntr_smul]
      have h2 : ntr ((c • (I • Y)) * X * Im) = c * ntr ((I • Y) * X * Im) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, ntr_smul]
      rw [h1, h2]
      ring)

def sym2 {M : Type*} [AddCommGroup M] [Module ℝ M] (β : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) :
    M →ₗ[ℝ] M →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (1 / 2 : ℝ) * (β x y + β y x))
    (fun x1 x2 y => by simp only [map_add, LinearMap.add_apply]; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
    (fun x y1 y2 => by simp only [map_add, LinearMap.add_apply]; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

lemma sym2_diag {M : Type*} [AddCommGroup M] [Module ℝ M] (β : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (x : M) :
    sym2 β x x = β x x := by
  rw [sym2, LinearMap.mk₂_apply]
  ring

lemma quadLM_diag (M X : Matrix (Fin 2) (Fin 2) ℂ) : quadLM M X X = ntr (X * X * M) := by
  rw [quadLM, LinearMap.mk₂_apply]
  ring

/-- Polarisation of `deltaPrimeAt`: its diagonal is the plaquette summand of `deltaPrimeSum`. -/
def deltaPrimeBilLM (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) :
    (Bond L → Vec) →ₗ[ℝ] (Bond L → Vec) →ₗ[ℝ] ℝ :=
  let iC := smulILM ∘ₗ toMLM ∘ₗ curlAt U p
  let β := brLM (imH U p)
  (quadLM (reH U p - 1)).compl₁₂ iC iC
    + β.compl₁₂ (edge1 U p) (edge2 U p)
    + β.compl₁₂ (edge1 U p) (edge3 U p)
    + β.compl₁₂ (edge1 U p) (edge4 U p)
    + β.compl₁₂ (edge2 U p) (edge3 U p)
    + β.compl₁₂ (edge2 U p) (edge4 U p)
    + β.compl₁₂ (edge3 U p) (edge4 U p)

lemma deltaPrimeBilLM_self (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A : Bond L → Vec) (p : Plaq L) :
    deltaPrimeBilLM U p A A = deltaPrimeAt U A p := by
  simp only [deltaPrimeBilLM, LinearMap.add_apply, LinearMap.compl₁₂_apply, quadLM_diag, brLM,
    LinearMap.mk₂_apply, smulILM, toMLM, curlAt, edge1, edge2, edge3, edge4, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  unfold deltaPrimeAt
  rfl

lemma curlM_add' (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → Vec) (p : Plaq L) :
    curlM U (A + B) p = curlM U A p + curlM U B p := by
  have : A + B = fun b => A b + B b := funext fun _ => rfl
  rw [this, curlM_add]

def plaqFin (P : Set (Plaq L)) : Finset (Plaq L) :=
  Finset.univ.filter fun p => p ∈ P

def curlBil (P : Set (Plaq L)) (U : Cfg L) : Field L →ₗ[ℝ] Field L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun A B => ∑ p ∈ plaqFin P, ⟪curlM (matU U) (ofBond A) p, curlM (matU U) (ofBond B) p⟫)
    (fun A A' B => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_add, curlM_add', inner_add_left])
    (fun c A B => by
      rw [map_smul]
      have h : ∀ p, curlM (matU U) (c • ofBond A) p = c • curlM (matU U) (ofBond A) p :=
        fun p => curlM_smul _ c _ p
      have hmul : ∀ p ∈ plaqFin P,
          ⟪curlM (matU U) (c • ofBond A) p, curlM (matU U) (ofBond B) p⟫ =
            c * ⟪curlM (matU U) (ofBond A) p, curlM (matU U) (ofBond B) p⟫ := by
        intro p hp
        rw [h p, inner_smul_left, starRingEnd_apply, star_trivial]
      rw [Finset.sum_congr rfl hmul]
      simp_rw [← smul_eq_mul]
      rw [← Finset.smul_sum])
    (fun A B B' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_add, curlM_add', inner_add_right])
    (fun c A B => by
      rw [map_smul]
      have h : ∀ p, curlM (matU U) (c • ofBond B) p = c • curlM (matU U) (ofBond B) p :=
        fun p => curlM_smul _ c _ p
      have hmul : ∀ p ∈ plaqFin P,
          ⟪curlM (matU U) (ofBond A) p, curlM (matU U) (c • ofBond B) p⟫ =
            c * ⟪curlM (matU U) (ofBond A) p, curlM (matU U) (ofBond B) p⟫ := by
        intro p hp
        rw [h p, inner_smul_right]
      rw [Finset.sum_congr rfl hmul]
      simp_rw [← smul_eq_mul]
      rw [← Finset.smul_sum])

def primeBil (P : Set (Plaq L)) (U : Cfg L) : Field L →ₗ[ℝ] Field L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun A B => ∑ p ∈ plaqFin P, deltaPrimeBilLM (matU U) p (ofBond A) (ofBond B))
    (fun A A' B => by
      rw [map_add]
      simp only [LinearMap.map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c A B => by
      rw [map_smul]
      have h : ∀ p, deltaPrimeBilLM (matU U) p (c • ofBond A) (ofBond B) =
          c • deltaPrimeBilLM (matU U) p (ofBond A) (ofBond B) :=
        fun p => by
          have h1 := congr_arg (fun f : (Bond L → Vec) →ₗ[ℝ] ℝ => f (ofBond B))
            ((deltaPrimeBilLM (matU U) p).map_smul c (ofBond A))
          exact h1
      simp_rw [h, Finset.smul_sum])
    (fun A B B' => by
      rw [map_add]
      have h : ∀ p, deltaPrimeBilLM (matU U) p (ofBond A) (ofBond B + ofBond B') =
          deltaPrimeBilLM (matU U) p (ofBond A) (ofBond B) +
            deltaPrimeBilLM (matU U) p (ofBond A) (ofBond B') :=
        fun p => (deltaPrimeBilLM (matU U) p (ofBond A)).map_add _ _
      simp_rw [h, Finset.sum_add_distrib])
    (fun c A B => by
      rw [map_smul]
      have h : ∀ p, deltaPrimeBilLM (matU U) p (ofBond A) (c • ofBond B) =
          c • deltaPrimeBilLM (matU U) p (ofBond A) (ofBond B) :=
        fun p => (deltaPrimeBilLM (matU U) p (ofBond A)).map_smul c (ofBond B)
      simp_rw [h, Finset.smul_sum])

/-- `Δ = D*D + Δ'` on the plaquettes of `P` (`plaqIn Ω₀` in the lemma). -/
def DeltaOp (P : Set (Plaq L)) (U : Cfg L) : Field L →L[ℝ] Field L :=
  symmOp (curlBil P U) + symmOp (primeBil P U)

theorem inner_primeOp (P : Set (Plaq L)) (U : Cfg L) (A : Field L) :
    ⟪A, symmOp (primeBil P U) A⟫ = deltaPrimeSum P (matU U) (ofField A) := by
  rw [inner_symmOp_diag]
  simp only [primeBil, LinearMap.mk₂_apply, deltaPrimeBilLM_self]
  unfold deltaPrimeSum
  rfl

/-! ## Level composite of the jets, and the bond space `𝔅` -/

def D2CompLM (ell : ℕ) (bg : ℕ → Cfg L) :
    ℕ → (Bond L → Vec) →ₗ[ℝ] (Bond L → Vec) →ₗ[ℝ] (Bond L → Vec)
  | 0 => 0
  | j + 1 =>
    LinearMap.mk₂ ℝ
      (fun a b =>
        (QlinStep (ell ^ j) ell (bg j)) (D2CompLM ell bg j a b)
          + D2Step (ell ^ j) ell (bg j) ((QlinComp ell bg j) a) ((QlinComp ell bg j) b))
      (fun a a' b => by
        funext c
        rw [LinearMap.map_add, LinearMap.add_apply, map_add, map_add (f := QlinComp ell bg j),
          D2Step_add_left]
        simp only [Pi.add_apply]
        abel)
      (fun r a b => by
        funext c
        rw [LinearMap.map_smul, LinearMap.smul_apply,
          map_smul (f := QlinStep (ell ^ j) ell (bg j)),
          map_smul (f := QlinComp ell bg j), D2Step_smul_left]
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ← smul_add, Pi.smul_apply, Pi.add_apply])
      (fun a b b' => by
        funext c
        rw [LinearMap.map_add, map_add (f := QlinStep (ell ^ j) ell (bg j)),
          map_add (f := QlinComp ell bg j), D2Step_add_right]
        simp only [Pi.add_apply]
        abel)
      (fun r a b => by
        funext c
        rw [map_smul (f := QlinComp ell bg j), D2Step_smul_right,
          (D2CompLM ell bg j a).map_smul, map_smul (f := QlinStep (ell ^ j) ell (bg j))]
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ← smul_add, Pi.smul_apply, Pi.add_apply])

def stratum (ell : ℕ) (S : Tower L) (j : ℕ) : Set (Site L) :=
  {x | (∀ μ, ell ^ j ∣ (x μ).val) ∧ x ∈ S.Om j ∧ x ∉ S.Om (j + 1)}

def OmGe (ell k : ℕ) (Lam : ℕ → Set (Site L)) (j : ℕ) (x : Site L) : Prop :=
  ∃ i, j ≤ i ∧ i ≤ k ∧ ∃ y ∈ Lam i, ∀ μ,
    (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell ^ i

/-- Level-`j` bonds of `𝔅`: touching `Λⱼ`, missing `Ω_{j+1}`. -/
def bondsLam (ell k : ℕ) (Lam : ℕ → Set (Site L)) (j : ℕ) : Set (Bond L) :=
  {b | (b.1 ∈ Lam j ∨ coarseShift b.1 (ell ^ j) b.2 ∈ Lam j) ∧
    ¬ (OmGe ell k Lam (j + 1) b.1 ∨ OmGe ell k Lam (j + 1) (coarseShift b.1 (ell ^ j) b.2))}

abbrev BIdx (ell k : ℕ) (Lam : ℕ → Set (Site L)) :=
  Σ j : Fin (k + 1), {b : Bond L // b ∈ bondsLam ell k Lam j}

noncomputable instance (ell k : ℕ) (Lam : ℕ → Set (Site L)) : Fintype (BIdx ell k Lam) := by
  classical
  infer_instance

abbrev FSp (ell k : ℕ) (Lam : ℕ → Set (Site L)) :=
  PiLp 2 (fun _ : BIdx ell k Lam => Vec)

noncomputable instance (ell k : ℕ) (Lam : ℕ → Set (Site L)) :
    FiniteDimensional ℝ (FSp ell k Lam) := inferInstance

instance (ell k : ℕ) (Lam : ℕ → Set (Site L)) : CompleteSpace (FSp ell k Lam) :=
  FiniteDimensional.complete ℝ _

def Qplain (ell k : ℕ) (bg : ℕ → Cfg L) (Lam : ℕ → Set (Site L)) :
    (Bond L → Vec) →ₗ[ℝ] FSp ell k Lam where
  toFun A := WithLp.toLp 2 fun p =>
    ((ell : ℝ) ^ p.1.val)⁻¹ • (QlinComp ell bg p.1.val A) p.2.1
  map_add' A A' := by
    refine PiLp.ext fun p => ?_
    simp only [WithLp.ofLp_toLp, PiLp.add_apply]
    rw [map_add, Pi.add_apply, smul_add]
  map_smul' c A := by
    refine PiLp.ext fun p => ?_
    simp only [WithLp.ofLp_toLp, PiLp.smul_apply]
    rw [map_smul, Pi.smul_apply, smul_comm]
    simp [RingHom.id_apply]

def Qfull (ell k : ℕ) (bg : ℕ → Cfg L) (Lam : ℕ → Set (Site L)) :
    Field L →L[ℝ] FSp ell k Lam :=
  LinearMap.toContinuousLinearMap (Qplain ell k bg Lam ∘ₗ ofBond)

/-- `C^{(2)}(A)(j,b) = ℓ^{-j} (½ D²_j(A,A))(b)`, bilinear in the two arguments. -/
def C2bil (ell k : ℕ) (bg : ℕ → Cfg L) (Lam : ℕ → Set (Site L)) :
    Field L →ₗ[ℝ] Field L →ₗ[ℝ] FSp ell k Lam :=
  LinearMap.mk₂ ℝ
    (fun A B => WithLp.toLp 2 fun p =>
      ((ell : ℝ) ^ p.1.val)⁻¹ • (1 / 2 : ℝ) • (D2CompLM ell bg p.1.val (ofBond A) (ofBond B)) p.2.1)
    (fun A A' B => by
      refine PiLp.ext fun p => ?_
      simp only [WithLp.ofLp_toLp, PiLp.add_apply]
      rw [map_add, LinearMap.map_add]
      rw [LinearMap.add_apply (D2CompLM ell bg p.1.val (ofBond A))
        (D2CompLM ell bg p.1.val (ofBond A')) (ofBond B)]
      rw [Pi.add_apply, smul_add, smul_add])
    (fun c A B => by
      refine PiLp.ext fun p => ?_
      simp only [WithLp.ofLp_toLp, PiLp.smul_apply]
      rw [map_smul, LinearMap.map_smul]
      rw [LinearMap.smul_apply]
      rw [Pi.smul_apply]
      have hcoef : ((ell : ℝ) ^ p.1.val)⁻¹ * (1 / 2) * c =
          c * (((ell : ℝ) ^ p.1.val)⁻¹ * (1 / 2)) := by ring
      rw [smul_smul, smul_smul, hcoef, smul_smul, smul_smul, ← mul_assoc])
    (fun A B B' => by
      refine PiLp.ext fun p => ?_
      simp only [WithLp.ofLp_toLp, PiLp.add_apply]
      rw [map_add, (D2CompLM ell bg p.1.val (ofBond A)).map_add (ofBond B) (ofBond B')]
      rw [Pi.add_apply, smul_add, smul_add])
    (fun c A B => by
      refine PiLp.ext fun p => ?_
      simp only [WithLp.ofLp_toLp, PiLp.smul_apply]
      rw [map_smul]
      rw [(D2CompLM ell bg p.1.val (ofBond A)).map_smul c (ofBond B)]
      rw [Pi.smul_apply]
      have hcoef : ((ell : ℝ) ^ p.1.val)⁻¹ * (1 / 2) * c =
          c * (((ell : ℝ) ^ p.1.val)⁻¹ * (1 / 2)) := by ring
      rw [smul_smul, smul_smul, hcoef, smul_smul, smul_smul, ← mul_assoc])

def bondsTouch (S : Set (Site L)) : Set (Bond L) :=
  {b | b.1 ∈ S ∨ shift b.1 b.2 ∈ S}

def bondMask (S : Set (Site L)) : Field L →L[ℝ] Field L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2 fun b => if b ∈ bondsTouch S then (WithLp.ofLp A) b else 0
      map_add' := fun A B => by
        refine PiLp.ext fun b => ?_
        simp only [WithLp.ofLp_toLp, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := fun c A => by
        refine PiLp.ext fun b => ?_
        simp only [WithLp.ofLp_toLp, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

/-- `W = I − D G' R D*`. -/
def Wop (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : Field L →L[ℝ] Field L :=
  1 - (gradL U).comp ((Gp ell k bg Om0 Lam U a).comp
    ((Rproj ell k bg Om0 Lam U).comp (gradAdj U)))

/-- `Δ_π = W* Δ W`, with `Δ` summed on `plaqIn Ω₀`. -/
def Dpi (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : Field L →L[ℝ] Field L :=
  (ContinuousLinearMap.adjoint (Wop ell k bg Om0 Lam U a)).comp
    ((DeltaOp (plaqIn Om0) U).comp (Wop ell k bg Om0 Lam U a))

def diagW (ell k : ℕ) (Lam : ℕ → Set (Site L)) (w : BIdx ell k Lam → ℝ) :
    FSp ell k Lam →L[ℝ] FSp ell k Lam :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun p => w p • f p
      map_add' := fun f g => by
        refine PiLp.ext fun p => ?_
        simp only [WithLp.ofLp_toLp, PiLp.add_apply, smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext fun p => ?_
        simp only [WithLp.ofLp_toLp, PiLp.smul_apply]
        rw [smul_comm, RingHom.id_apply] }

def massW (ell : ℕ) (a : ℝ) {k : ℕ} {Lam : ℕ → Set (Site L)} (p : BIdx ell k Lam) : ℝ :=
  a * (ell : ℝ) ^ p.1.val

/-- `Q* a Q` with weight `a ℓ^j`. -/
def MassFull (ell k : ℕ) (bg : ℕ → Cfg L) (Lam : ℕ → Set (Site L)) (a : ℝ) :
    Field L →L[ℝ] Field L :=
  (ContinuousLinearMap.adjoint (Qfull ell k bg Lam)).comp
    ((diagW ell k Lam (massW ell a)).comp (Qfull ell k bg Lam))

/-- `T = R D*` on fields supported on bonds touching `Ω₀`. -/
def Tfull (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) : Field L →L[ℝ] SiteL2 L :=
  (Rproj ell k bg Om0 Lam U).comp ((gradAdj U).comp (bondMask Om0))

/-- `Q` on that bond space. -/
def Qe (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L)) :
    Field L →L[ℝ] FSp ell k Lam :=
  (Qfull ell k bg Lam).comp (bondMask Om0)

def Qs (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L)) :
    FSp ell k Lam →L[ℝ] Field L :=
  ContinuousLinearMap.adjoint (Qe ell k bg Om0 Lam)

/-- `G⁻¹ = Δ_π + DRD* + Q*aQ`, padded by the identity off the Dirichlet bond space
so that `Ring.inverse` inverts on that space and is `0` after the final mask. -/
def Ginv (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : Field L →L[ℝ] Field L :=
  (bondMask Om0).comp ((Dpi ell k bg Om0 Lam U a).comp (bondMask Om0))
    + (ContinuousLinearMap.adjoint (Tfull ell k bg Om0 Lam U)).comp (Tfull ell k bg Om0 Lam U)
    + (bondMask Om0).comp ((MassFull ell k bg Lam a).comp (bondMask Om0))
    + (1 - bondMask Om0)

def GE (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : Field L →L[ℝ] Field L :=
  (Ring.inverse (Ginv ell k bg Om0 Lam U a)).comp (bondMask Om0)

/-- `H = G Q* (QG Q*)⁻¹`. -/
def HE (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : FSp ell k Lam →L[ℝ] Field L :=
  ((GE ell k bg Om0 Lam U a).comp (Qs ell k bg Om0 Lam)).comp
    (Ring.inverse (((Qe ell k bg Om0 Lam).comp (GE ell k bg Om0 Lam U a)).comp
      (Qs ell k bg Om0 Lam)))

def JF (Om0 : Set (Site L)) (U : Cfg L) : Field L :=
  bondMask Om0 (Jfield (plaqIn Om0) U)

/-- Bilinear form of (3.128). -/
def betaK (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : Field L →ₗ[ℝ] Field L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y =>
      ⟪x, bondMask Om0 (Dpi ell k bg Om0 Lam U a (bondMask Om0 y))⟫
        - 2 * ⟪HE ell k bg Om0 Lam U a
            (C2bil ell k bg Lam (Wop ell k bg Om0 Lam U a (bondMask Om0 x))
              (Wop ell k bg Om0 Lam U a (bondMask Om0 y))), JF Om0 U⟫
        + ⟪Tfull ell k bg Om0 Lam U x, Tfull ell k bg Om0 Lam U y⟫
        + ⟪x, bondMask Om0 (MassFull ell k bg Lam a (bondMask Om0 y))⟫)
    (fun x1 x2 y => by
      rw [inner_add_left]
      rw [map_add (bondMask Om0), map_add (Wop ell k bg Om0 Lam U a),
        LinearMap.map_add (C2bil ell k bg Lam), LinearMap.add_apply,
        map_add (HE ell k bg Om0 Lam U a), inner_add_left]
      rw [map_add (Tfull ell k bg Om0 Lam U), inner_add_left, inner_add_left]
      ring)
    (fun c x y => by
      rw [inner_smul_left]
      rw [map_smul (bondMask Om0), map_smul (Wop ell k bg Om0 Lam U a),
        LinearMap.map_smul (C2bil ell k bg Lam), LinearMap.smul_apply,
        map_smul (HE ell k bg Om0 Lam U a), inner_smul_left]
      rw [map_smul (Tfull ell k bg Om0 Lam U), inner_smul_left, inner_smul_left]
      rw [starRingEnd_apply, star_trivial]
      ring)
    (fun x y1 y2 => by
      rw [map_add (bondMask Om0), map_add (Dpi ell k bg Om0 Lam U a), map_add (bondMask Om0),
        inner_add_right]
      rw [map_add (Wop ell k bg Om0 Lam U a), LinearMap.map_add,
        map_add (HE ell k bg Om0 Lam U a), inner_add_left]
      rw [map_add (Tfull ell k bg Om0 Lam U), inner_add_right]
      rw [map_add (MassFull ell k bg Lam a), map_add (bondMask Om0), inner_add_right]
      ring)
    (fun c x y => by
      rw [map_smul (bondMask Om0), map_smul (Dpi ell k bg Om0 Lam U a), map_smul (bondMask Om0),
        inner_smul_right]
      rw [map_smul (Wop ell k bg Om0 Lam U a), LinearMap.map_smul,
        map_smul (HE ell k bg Om0 Lam U a), inner_smul_left]
      rw [map_smul (Tfull ell k bg Om0 Lam U), inner_smul_right]
      rw [map_smul (MassFull ell k bg Lam a), map_smul (bondMask Om0), inner_smul_right]
      rw [starRingEnd_apply, star_trivial]
      ring)

/-- The symmetric operator of (3.128), inverted on the Dirichlet bond space. -/
def G1 (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : Field L →L[ℝ] Field L :=
  (Ring.inverse (bondMask Om0 ∘L symmOp (betaK ell k bg Om0 Lam U a) ∘L bondMask Om0
      + (1 - bondMask Om0))).comp (bondMask Om0)

/-- `H₁ = G₁ Q* (Q G₁ Q*)⁻¹`. -/
def H1E (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : FSp ell k Lam →L[ℝ] Field L :=
  ((G1 ell k bg Om0 Lam U a).comp (Qs ell k bg Om0 Lam)).comp
    (Ring.inverse (((Qe ell k bg Om0 Lam).comp (G1 ell k bg Om0 Lam U a)).comp
      (Qs ell k bg Om0 Lam)))

/-- `Q G₁ Q*` on `𝔅`. -/
def Nmat (ell k : ℕ) (bg : ℕ → Cfg L) (Om0 : Set (Site L)) (Lam : ℕ → Set (Site L))
    (U : Cfg L) (a : ℝ) : FSp ell k Lam →L[ℝ] FSp ell k Lam :=
  ((Qe ell k bg Om0 Lam).comp (G1 ell k bg Om0 Lam U a)).comp (Qs ell k bg Om0 Lam)

/-! ## Unit torus: `τ`, `Q₁`, `C = id − h Q₁` -/

def embY (ell k : ℕ) (Lu : Extent) (y : Site Lu) : Site (scaleUp ell k Lu) :=
  fun μ => ⟨ell ^ k * (y μ).val, by
    have hy : (y μ).val < Lu μ + 1 := (y μ).isLt
    unfold scaleUp
    by_cases h0 : ell ^ k = 0
    · simp [h0]
    · have hpos : 0 < (Lu μ + 1) * ell ^ k :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.pos_of_ne_zero h0)
      rw [Nat.sub_add_cancel (Nat.one_le_of_lt hpos)]
      have hlt : ell ^ k * (y μ).val < ell ^ k * (Lu μ + 1) :=
        Nat.mul_lt_mul_of_pos_left hy (Nat.pos_of_ne_zero h0)
      simpa [Nat.mul_comm] using hlt⟩

def unitBond (ell k : ℕ) (Lu : Extent) (e : Bond Lu) : Bond (scaleUp ell k Lu) :=
  (embY ell k Lu e.1, e.2)

def tauPlain (ell k : ℕ) (Lu : Extent) (Lam : ℕ → Set (Site (scaleUp ell k Lu))) :
    FSp ell k Lam →ₗ[ℝ] (Bond Lu → Vec) where
  toFun f := fun e =>
    if h : unitBond ell k Lu e ∈ bondsLam ell k Lam k then
      f ⟨⟨k, Nat.lt_succ_self k⟩, ⟨unitBond ell k Lu e, h⟩⟩
    else 0
  map_add' f g := by
    funext e
    by_cases h : unitBond ell k Lu e ∈ bondsLam ell k Lam k
    · simp [h, Pi.add_apply]
    · simp [h]
  map_smul' c f := by
    funext e
    by_cases h : unitBond ell k Lu e ∈ bondsLam ell k Lam k
    · simp [h, Pi.smul_apply, RingHom.id_apply]
    · simp [h, RingHom.id_apply]

def tau (ell k : ℕ) (Lu : Extent) (Lam : ℕ → Set (Site (scaleUp ell k Lu))) :
    FSp ell k Lam →L[ℝ] Field Lu :=
  LinearMap.toContinuousLinearMap (toBond ∘ₗ tauPlain ell k Lu Lam)

abbrev CoarseBond (ell : ℕ) := {c : Bond L // c.1 ∈ CoarseLattice (L := L) ell}

abbrev Drow (ell : ℕ) (Lam : Set (Site L)) :=
  {c : CoarseBond (L := L) ell // CRowIn ell Lam c.1}

noncomputable instance (ell : ℕ) (Lam : Set (Site L)) : Fintype (Drow (L := L) ell Lam) := by
  classical
  infer_instance

def iotaD (ell : ℕ) (Lam : Set (Site L)) : (Drow (L := L) ell Lam → Vec) →ₗ[ℝ] (Bond L → Vec) where
  toFun w := fun b => ∑ c : Drow (L := L) ell Lam, if b = droppedBond ell c.1.1 then w c else 0
  map_add' w w' := by
    funext b
    rw [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hb
    · rw [Pi.add_apply]
    · rw [zero_add]
  map_smul' r w := by
    funext b
    rw [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hb
    · rw [Pi.smul_apply]
    · rw [smul_zero]

def rhoD (ell : ℕ) (Lam : Set (Site L)) :
    (CoarseBond (L := L) ell → Vec) →ₗ[ℝ] (Drow (L := L) ell Lam → Vec) where
  toFun f := fun c => f c.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Q1LM (ell : ℕ) (V0 : Cfg L) : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec) where
  toFun B := fun c => ((ell : ℝ)⁻¹) • (QlinStep 1 ell V0 B) c.1
  map_add' A B := by funext c; simp only [map_add, Pi.add_apply, smul_add]
  map_smul' r A := by
    funext c
    rw [Pi.smul_apply, map_smul, Pi.smul_apply, smul_comm, RingHom.id_apply]

def H0 (ell : ℕ) (Lam : Set (Site L))
    (Q : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec)) :
    (Drow (L := L) ell Lam → Vec) →ₗ[ℝ] (Drow (L := L) ell Lam → Vec) :=
  rhoD ell Lam ∘ₗ Q ∘ₗ iotaD ell Lam

/-- `H₀⁻¹`, or `0` when `H₀` is not bijective. -/
def H0inv (ell : ℕ) (Lam : Set (Site L))
    (Q : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec)) :
    (Drow (L := L) ell Lam → Vec) →ₗ[ℝ] (Drow (L := L) ell Lam → Vec) :=
  if h : Function.Bijective (H0 ell Lam Q) then
    (LinearEquiv.ofBijective (H0 ell Lam Q) h).symm.toLinearMap
  else 0

/-- Corridor lift. It is `0` when `H₀` is not bijective. -/
def hLift (ell : ℕ) (Lam : Set (Site L))
    (Q : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec)) :
    (CoarseBond (L := L) ell → Vec) →ₗ[ℝ] (Bond L → Vec) :=
  iotaD ell Lam ∘ₗ H0inv ell Lam Q ∘ₗ rhoD ell Lam

/-- `C = id − h Q₁`. -/
def Cop (ell : ℕ) (Lam : Set (Site L))
    (Q : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec)) :
    (Bond L → Vec) →ₗ[ℝ] (Bond L → Vec) :=
  LinearMap.id - hLift ell Lam Q ∘ₗ Q

def C2tilde (ell : ℕ) (V0 : Cfg L) (B : Bond L → Vec) : CoarseBond (L := L) ell → Vec :=
  fun c => C2Step 1 ell V0 B c.1

def D2plain (ell : ℕ) (Lam : Set (Site L)) (V0 : Cfg L) (B : Bond L → Vec) : Bond L → Vec :=
  ((ell : ℝ)⁻¹) • hLift ell Lam (Q1LM ell V0) (C2tilde ell V0 B)

/-! ## One point of the lemma, and `genForm` -/

structure Prm where
  ell : ℕ
  k : ℕ
  Lu : Extent
  S : Tower (scaleUp ell k Lu)
  U : Cfg (scaleUp ell k Lu)
  a : ℝ
  Lam : Set (Site Lu)

def Prm.Lf (P : Prm) : Extent := scaleUp P.ell P.k P.Lu

def Prm.bg (P : Prm) : ℕ → Cfg P.Lf := bgTower P.ell P.U

def Prm.strata (P : Prm) : ℕ → Set (Site P.Lf) := stratum P.ell P.S

def Prm.eta (P : Prm) : ℝ := ((P.ell : ℝ) ^ P.k)⁻¹

/-- Unit-level background: the `k`-fold blocked configuration `Ū^k` read at the unit
bonds (the frozen lane's `IngrBParams.unitBgU`), NOT the raw `U`. -/
def Prm.unitV (P : Prm) : Cfg P.Lu := fun e => P.bg P.k (unitBond P.ell P.k P.Lu e)

def Prm.Q1 (P : Prm) : (Bond P.Lu → Vec) →ₗ[ℝ] (CoarseBond (L := P.Lu) P.ell → Vec) :=
  Q1LM P.ell P.unitV

def Prm.genC (P : Prm) : (Bond P.Lu → Vec) →ₗ[ℝ] (Bond P.Lu → Vec) :=
  Cop P.ell P.Lam P.Q1

def Prm.H1in (P : Prm) : Field P.Lu →L[ℝ] Field P.Lf :=
  (H1E P.ell P.k P.bg (P.S.Om 0) P.strata P.U P.a).comp
    (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata))

def Prm.Jf (P : Prm) : Field P.Lf := Jfield (plaqIn (P.S.Om 0)) P.U

/-- (3.156): `η ⟨τ* B, (Q G₁ Q*)⁻¹ τ* B⟩ − a ⟨B, B⟩ − 2 ⟨H₁ D̃⁽²⁾(B), J⟩`. -/
def genForm (P : Prm) (B : Field P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B,
      Ring.inverse (Nmat P.ell P.k P.bg (P.S.Om 0) P.strata P.U P.a)
        (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B)⟫
    - P.a * ⟪B, B⟫
    - 2 * ⟪P.H1in (toField (D2plain P.ell P.Lam P.unitV (ofField B))), P.Jf⟫

end

end BalabanCompact
