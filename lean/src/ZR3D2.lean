import ZR3D1

/-!
# R3D2 -- the strengthened ingredient class `IngrB3` and the MUST-FIRE theorem `not_IngrB3_goodFam`.

Two NEW laws on the abstract base data inside `IngrBAt`, both holding for the printed objects:
* `FlatDpiLaw`  (Δ_π / curvature-term law): at the trivial configuration `U = 1` (so `J = 0`,
  `Δ' = 0`, (3.10)) and `Ω₀ = T`, `⟨A, Δ_π A⟩ = ‖D_U^1 A‖²` by (3.119)-(3.120) (`curl ∘ D = 0`), so
  `curl A = 0 ⇒ ⟨A, Δ_π A⟩ = 0` (normalisation-free).
* `TKerLaw`  (relation to RD*): `T = R D*` with `R` linear, hence `T` kills `ker D*`, i.e. every `A`
  with `⟨A, D_U λ⟩ = 0 ∀ λ`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantHjMinimizer (SiteFnL2 trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.IngredientFamily (BaseData JSU2 JSU2_trivial)
open scoped RealInnerProductSpace

/-- Δ_π-law at a configuration where `curl`-form is the whole Hessian -/
def FlatDpiLaw {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L) : Prop :=
  ∀ A : BondFnL2 L, curlCovariantCLM_L2 U A = 0 → ⟪A, Dpi A⟫ = 0

/-- `T = R D*` kills `ker D*` -/
def TKerLaw {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (T : BondFnL2 L →L[ℝ] BondFnL2 L) : Prop :=
  ∀ A : BondFnL2 L, (∀ lam : SiteFnL2 L, ⟪A, gradL2 U lam⟫ = 0) → T A = 0

/-- `IngrB` + the two flat-point laws (imposed at `U = 1`, `Ω₀ = T`, for the `T_ker` law at every `U`). -/
structure IngrB3 (ell : ℕ) (hell : 0 < ell) (I : IngrFamK ell) where
  toB : IngrB ell hell I
  dpi_law : ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)), S.Om 0 = Set.univ →
    FlatDpiLaw (trivialU (scaleUp ell k Lu)) (toB.at_ k Lu hd S (trivialU (scaleUp ell k Lu)) Lam).base.Dpi
  t_law : ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)), S.Om 0 = Set.univ →
    TKerLaw U (toB.at_ k Lu hd S U Lam).base.T

theorem nontrivial_bondFnL2 (L : PeriodicLatticeExtent) : Nontrivial (BondFnL2 L) :=
  ⟨⟨constField L suTwoWitness, 0, by
    intro h
    have := constField_norm_pos (L := L) suTwoWitness suTwoWitness_ne_zero
    rw [h] at this; simp at this⟩⟩

/-- the whole contradiction, for an arbitrary witness `A` of `IngrBAt` over `goodIngr'` at `U = 1` -/
theorem no_witness (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (Lam : Set (PeriodicLatticeSite Lu))
    (Ub : LinkCfg Lu)
    (I : Ingr ell Lu (scaleUp ell k Lu) Lam)
    (hI : I = goodIngr' ell hell k Lu (trivialU (scaleUp ell k Lu)) hd Lam)
    (A : IngrBAt ell hell k Lu Lam (trivialU (scaleUp ell k Lu)) Ub I)
    (hP : FlatDpiLaw (trivialU (scaleUp ell k Lu)) A.base.Dpi)
    (hT : TKerLaw (trivialU (scaleUp ell k Lu)) A.base.T) : False := by
  subst hI
  haveI : Nontrivial (BondFnL2 (scaleUp ell k Lu)) := nontrivial_bondFnL2 _
  set Q := Qclm ell hell k Lu (trivialU (scaleUp ell k Lu)) with hQ
  set c : BondFnL2 (scaleUp ell k Lu) := constField _ suTwoWitness with hc
  -- Step 1: the witness's G1inv is the good one
  have hGood : (goodBase ell hell k Lu (trivialU (scaleUp ell k Lu))).Ginv =
      (1 : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu)) +
        (ContinuousLinearMap.adjoint Q).comp Q := goodBase_Ginv ell hell k Lu _
  obtain ⟨u, hu⟩ := Ginv_unit Q
  have hG1good : (goodIngr' ell hell k Lu (trivialU (scaleUp ell k Lu)) hd Lam).G1 = ↑u⁻¹ := by
    show Ring.inverse (goodBase ell hell k Lu (trivialU (scaleUp ell k Lu))).Ginv = _
    rw [hGood, ← hu, Ring.inverse_unit]
  have hEq := A.G1_eq
  rw [hG1good] at hEq
  have hunit : IsUnit A.G1inv := by
    by_contra hnu
    rw [Ring.inverse_non_unit _ hnu] at hEq
    have h1 : (1 : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu)) = 0 := by
      have := congrArg (fun T => (u : _ →L[ℝ] _) * T) hEq
      simp only [Units.mul_inv, mul_zero] at this
      exact this
    obtain ⟨y, hy⟩ := exists_ne (0 : BondFnL2 (scaleUp ell k Lu))
    exact hy (by simpa using congrArg (fun T => T y) h1)
  obtain ⟨v, hv⟩ := hunit
  have hvu : v⁻¹ = u⁻¹ := by
    rw [← hv, Ring.inverse_unit] at hEq
    exact Units.ext hEq.symm
  have hvu' : v = u := inv_injective hvu
  have hG1inv : A.G1inv = ↑u := by rw [← hv, hvu']
  -- Step 2: K c
  have hform := A.G1inv_spec.form c
  have hJ : A.base.J = 0 := by
    rw [A.base_J]
    have h0 : JSU2 (((ell : ℝ) ^ k)⁻¹) (trivialU (scaleUp ell k Lu)) = 0 :=
      funext fun b => JSU2_trivial _ b
    show WithLp.toLp 2 (JSU2 (((ell : ℝ) ^ k)⁻¹) (trivialU (scaleUp ell k Lu))) = 0
    rw [h0]; rfl
  have hDpi : ⟪c, A.base.Dpi c⟫ = 0 := hP c (curl_const_trivial _)
  have hTc : A.base.T c = 0 := hT c (fun lam => const_orth_grad_trivial _ lam)
  have hK : A.base.K c = ‖Q c‖ ^ 2 := by
    unfold BaseData.K
    rw [hDpi, hTc, hJ, A.base_Q, A.base_a]
    simp only [inner_zero_right, mul_zero, norm_zero]
    show (0 : ℝ) - 0 + 0 ^ 2 + (goodIngr' ell hell k Lu (trivialU (scaleUp ell k Lu)) hd Lam).a *
      ‖(goodIngr' ell hell k Lu (trivialU (scaleUp ell k Lu)) hd Lam).Q c‖ ^ 2 = _
    show _ = ‖Q c‖ ^ 2
    have e1 : (goodIngr' ell hell k Lu (trivialU (scaleUp ell k Lu)) hd Lam).a = 1 := rfl
    have e2 : (goodIngr' ell hell k Lu (trivialU (scaleUp ell k Lu)) hd Lam).Q = Q := rfl
    rw [e1, e2]; ring
  -- Step 3: ⟨c, G1inv c⟩ = ‖c‖² + ‖Qc‖²
  have hlhs : ⟪c, A.G1inv c⟫ = ‖c‖ ^ 2 + ‖Q c‖ ^ 2 := by
    have hu' : A.G1inv = 1 + (ContinuousLinearMap.adjoint Q).comp Q := by rw [hG1inv, hu]
    rw [hu']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, inner_add_right]
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [hlhs, hK] at hform
  have hpos : 0 < ‖c‖ ^ 2 := constField_norm_pos _ suTwoWitness_ne_zero
  linarith

#print axioms no_witness

end AdalyFormal.StatementLane3
