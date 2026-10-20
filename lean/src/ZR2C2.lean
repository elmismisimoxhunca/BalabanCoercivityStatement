import ZR2C1

/-!
# R2C2 -- `IngrBAt` / `IngrB`: the ingredient class, and the MUST-FIRE theorems.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.FullReparamC (fullCLM dinvC)
open AdalyFormal.IngredientFamily (BaseData JSU2 D2unit)

/-- The ingredient-class at ONE point `(k, Lu, Λ, U)`: every field of `Ingr` is tied either to a
printed formula (pinned to a tree/ingredient-lane declaration) or to a printed law.
PINNED: `Q` (= `lineCoarseRestrictCov U (ell^k)` through the coarse-site embedding), `J` (= `JSU2`,
(3.11)), `Q1` (= covariant line-integral average at the unit background `Ub`, CMP96 (2.125)),
`C` (whole torus: `fullCLM`), `G1` (= inverse of the symmetric operator with the quadratic form
(3.128) of `base`), `H1` ((3.129)), `a > 0` ((3.24)), `D2` (second Taylor term of a raw map, lifted).
ABSTRACT: `base.Dpi`, `base.T` (Δ_π, R D*), `base.C2`, the value of `a`, the background `Ub`, `Qraw`,
`hlift`, and `C` for `Λ ≠ T`. -/
structure IngrBAt (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) (Ub : LinkCfg Lu)
    (I : Ingr ell Lu (scaleUp ell k Lu) Lam) where
  base : BaseData (BondFnL2 (scaleUp ell k Lu)) (BondFnL2 Lu)
  base_Q : base.Q = I.Q
  base_Qs : base.Qs = I.Qs
  base_a : base.a = I.a
  base_J : base.J = I.J
  a_pos : 0 < I.a
  J_eq : I.J = WithLp.toLp 2 (JSU2 (((ell : ℝ) ^ k)⁻¹) U)
  G1inv : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu)
  G1inv_spec : base.IsG1inv G1inv
  G1_eq : I.G1 = Ring.inverse G1inv
  H1_eq : I.H1 = (I.G1.comp I.Qs).comp (Ring.inverse ((I.Q.comp I.G1).comp I.Qs))
  Q_eq : ∀ (A : BondFnL2 (scaleUp ell k Lu)) (b : Bond Lu),
    (I.Q A).ofLp b = lineCoarseRestrictCov U (ell ^ k) A.ofLp
      ⟨⟨embSite ell hell k b.1, embSite_mem ell hell k b.1⟩, b.2⟩
  Q1_eq : I.Q1 = lineCoarseRestrictCovLM Ub ell
  C_univ : Lam = Set.univ → I.C = fullCLM Ub ell (dinvC Ub ell)
  Qraw : BondFnL2 Lu → (CoarseBond Lu ell → SuTwo)
  hlift : (CoarseBond Lu ell → SuTwo) →L[ℝ] BondFnL2 Lu
  D2_eq : I.D2 = D2unit hlift Qraw

/-- The ingredient-class for a family: for tiled unit tori, every point carries an `IngrBAt` with a
single family of backgrounds `Ubar` (CMP98 (89)/(43), abstract) with `Ubar 1 = 1`. -/
structure IngrB (ell : ℕ) (hell : 0 < ell) (I : IngrFamK ell) where
  Ubar : ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), LinkCfg (scaleUp ell k Lu) → LinkCfg Lu
  Ubar_one : ∀ k Lu, Ubar k Lu (fun _ => 1) = fun _ => 1
  at_ : ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), (∀ μ : Fin 3, ell ∣ Lu μ + 1) →
    ∀ (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
      (Lam : Set (PeriodicLatticeSite Lu)),
      IngrBAt ell hell k Lu Lam U (Ubar k Lu U) (I k Lu S U Lam)

/-! ## general consequences (used by the must-fire controls) -/

theorem bondFnL2_exists_ne_zero (Lu : PeriodicLatticeExtent) : ∃ y : BondFnL2 Lu, y ≠ 0 := by
  classical
  let b : Bond Lu := (fun μ => ⟨0, Nat.succ_pos _⟩, 0)
  refine ⟨WithLp.toLp 2 (Pi.single b suTwoWitness), fun h => ?_⟩
  have := congrArg (fun y : BondFnL2 Lu => y.ofLp b) h
  simp at this
  exact suTwoWitness_ne_zero this

theorem IngrBAt.Q_comp_H1 {ell : ℕ} {hell : 0 < ell} {k : ℕ} {Lu : PeriodicLatticeExtent}
    {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)} {Ub : LinkCfg Lu}
    {I : Ingr ell Lu (scaleUp ell k Lu) Lam} (h : IngrBAt ell hell k Lu Lam U Ub I) :
    I.Q.comp I.H1 = ContinuousLinearMap.id ℝ _ := by
  rw [h.H1_eq]
  have hu := I.QGQ_unit
  have : I.Q.comp ((I.G1.comp I.Qs).comp (Ring.inverse ((I.Q.comp I.G1).comp I.Qs)))
      = ((I.Q.comp I.G1).comp I.Qs) * Ring.inverse ((I.Q.comp I.G1).comp I.Qs) := by
    ext y; simp [ContinuousLinearMap.mul_def]
  rw [this]
  exact Ring.mul_inverse_cancel _ hu

/-- **MUST-FIRE (1).**  An ingredient with `H1 = 0` is not in the class (printed (3.129) forces
`Q H1 = id`), for ANY `Q, G1, Qs, ...`. -/
theorem IngrBAt.H1_ne_zero {ell : ℕ} {hell : 0 < ell} {k : ℕ} {Lu : PeriodicLatticeExtent}
    {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)} {Ub : LinkCfg Lu}
    {I : Ingr ell Lu (scaleUp ell k Lu) Lam} (h : IngrBAt ell hell k Lu Lam U Ub I) :
    I.H1 ≠ 0 := by
  intro h0
  obtain ⟨y, hy⟩ := bondFnL2_exists_ne_zero Lu
  have := congrArg (fun T => T y) h.Q_comp_H1
  simp [h0] at this
  exact hy this.symm

theorem not_IngrBAt_of_H1_zero {ell : ℕ} {hell : 0 < ell} {k : ℕ} {Lu : PeriodicLatticeExtent}
    {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)} {Ub : LinkCfg Lu}
    (I : Ingr ell Lu (scaleUp ell k Lu) Lam) (h0 : I.H1 = 0) :
    IsEmpty (IngrBAt ell hell k Lu Lam U Ub I) :=
  ⟨fun h => h.H1_ne_zero h0⟩

theorem not_IngrBAt_of_a_nonpos {ell : ℕ} {hell : 0 < ell} {k : ℕ} {Lu : PeriodicLatticeExtent}
    {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)} {Ub : LinkCfg Lu}
    (I : Ingr ell Lu (scaleUp ell k Lu) Lam) (h0 : I.a ≤ 0) :
    IsEmpty (IngrBAt ell hell k Lu Lam U Ub I) :=
  ⟨fun h => absurd h.a_pos (not_lt.mpr h0)⟩

/-- a family whose `H1` vanishes (or whose `a ≤ 0`) at some tiled point is NOT in the class -/
theorem IngrB.not_of_H1_zero {ell : ℕ} {hell : 0 < ell} (I : IngrFamK ell) (k : ℕ)
    (Lu : PeriodicLatticeExtent) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (S U Lam)
    (h0 : (I k Lu S U Lam).H1 = 0) : IsEmpty (IngrB ell hell I) :=
  ⟨fun B => (B.at_ k Lu hd S U Lam).H1_ne_zero h0⟩

theorem IngrB.not_of_a_nonpos {ell : ℕ} {hell : 0 < ell} (I : IngrFamK ell) (k : ℕ)
    (Lu : PeriodicLatticeExtent) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (S U Lam)
    (h0 : (I k Lu S U Lam).a ≤ 0) : IsEmpty (IngrB ell hell I) :=
  ⟨fun B => absurd (B.at_ k Lu hd S U Lam).a_pos (not_lt.mpr h0)⟩

#print axioms IngrBAt.H1_ne_zero
#print axioms IngrB.not_of_H1_zero

end AdalyFormal.StatementLane2
