import ZXR2Close0d
import ZR2D
import ZXR3F

/-!
# G3A -- `P428Genuine`: the printed claim (CMP99b p.428, (3.156)-(3.157)) stated for THE genuine
ingredient family (no `∃`/`∀` over ingredient families).  NOTHING HERE PROVES THE LEMMA.
Only definitions and structural implications.  No sorry / native_decide / axiom.

The genuine ingredients are the declarations of `compute/ingredient_family_20261009_r2`
(`IngrBParams`: `baseData`, `G1inv`, `H1in`, `D2in`, `Jf`, `Q1`, `Cop`, `tau`, `Qin`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

namespace GenP
variable (P : IngrBParams)

/-- `N = Q G₁ Q*` on the constraint space `L²(𝔅)`, with the MULTI-LEVEL `Q = (Q_j(U))_{j≤k}` of
(3.15)/(3.110) and the printed `G₁ = (G₁⁻¹)⁻¹`, `G₁⁻¹` the unique symmetric operator with form
(3.128).  This is the matrix the print inverts in (3.129)/(3.156). -/
noncomputable def Nmat : FSp P.G →L[ℝ] FSp P.G :=
  (P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs

/-- FEASIBILITY of the printed construction at one point `(k, S, U, Λ, a)`:
 (hb)  the constraint matrix `H₀` of (3.157) (coefficients of the dropped bonds `b₀(c)` in `Q₁`)
       is invertible, so that `C` and `h = L⁻¹ ι H₀⁻¹ ρ` of CMP109 p.267 exist;
 (hG)  `G₁⁻¹` of (3.128) is invertible (so `G₁` of (3.138) is the genuine inverse, not `Ring.inverse = 0`);
 (hN)  `Q G₁ Q*` is invertible on `𝔅` (the print writes `(QG₁Q*)⁻¹`). -/
def WellDef : Prop :=
  Function.Bijective (H0 P.Lam P.Q1) ∧ IsUnit P.G1inv ∧ IsUnit (Nmat P)

/-- The first term of (3.156), `⟨B,(QG₁Q*)⁻¹B⟩`, with `B` zero-extended from the unit bonds to
`L²(𝔅)` by `τ*` (`τ*` puts `B` at level `k`, zero at levels `j < k`; this is the print's `B ∈ 𝔅`
supported at the top level), in the lane's `η` normalisation (`G₁` of `Ingr` is `η⁻¹ ι G₁ ι*`, so the
inverse carries the factor `η`; `P.eta = L^{-k}`). -/
noncomputable def firstTerm (B : BondFnL2 P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (Nmat P) (ContinuousLinearMap.adjoint P.tau B)⟫

/-- **(3.156)**, genuine: `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩`. -/
noncomputable def genForm (B : BondFnL2 P.Lu) : ℝ :=
  firstTerm P B - P.a * ⟪B, B⟫ - 2 * ⟪P.H1in (P.D2in B), P.Jf⟫

/-- `C` of (3.157). -/
noncomputable def genC : (Bond P.Lu → SuTwo) →ₗ[ℝ] (Bond P.Lu → SuTwo) := Cop P.Lam P.Q1

end GenP

/-- the parameters of the genuine family at one point -/
abbrev gparams (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : IngrBParams :=
  ⟨ell, k, Lu, hell, S, U, a, Lam⟩

/-- **SUPERSEDED IN r5 (S75): this is the r3/r4-shaped inner claim (`k` unrestricted, `CoversOm0`/`PerCubeRegularMix` range class, `LambdaOK` without `Λ = B(Λ')`, `WellDef` in the conclusion). The r5 statement `CoercG5At` / `P428Genuine5` was superseded by the r6 statement `ZT5A.CoercG8At` / `P428Genuine8`. Kept only because downstream r4 evidence modules (`ZXG3B..N`, `ZGU1*`) are stated about `genForm` and do not use it.**
The claim at a FIXED `(k, Lu)` and constants `(α₀, γ₀)`, TOUCHING bond convention
(CMP96 p.245, Lemma 2.4 hypothesis sentence).  Feasibility (`WellDef`) is part of the CONCLUSION.
Hypotheses are those of the print: torus tiling, admissible tower, `Λ`, `U` in the per-cube class
(curl form of (3.36), cube-size cap `F`), `B̃ ∈ Λ̃`. -/
def CoercGenAt (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (F : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0 ell M F k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegularMix ell M F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    GenP.WellDef (gparams ell k Lu hell S U a Lam) ∧
    ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      γ₀ * bondEnergy Bt ≤
        GenP.genForm (gparams ell k Lu hell S U a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

/-- the same with the BOTH-ENDPOINT bond convention (`B̃ = 0` unless both endpoints lie in `Λ`) -/
def CoercGenAtBoth (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (F : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0 ell M F k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegularMix ell M F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    GenP.WellDef (gparams ell k Lu hell S U a Lam) ∧
    ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambda Lam Bt →
      γ₀ * bondEnergy Bt ≤
        GenP.genForm (gparams ell k Lu hell S U a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

theorem CoercGenAt.toBoth {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {F : ℕ} {α₀ γ₀ : ℝ} (h : CoercGenAt ell M R k hell a Lu F α₀ γ₀) :
    CoercGenAtBoth ell M R k hell a Lu F α₀ γ₀ := by
  intro hT S hS hC Lam hL U hU
  obtain ⟨hw, hb⟩ := h hT S hS hC Lam hL U hU
  exact ⟨hw, fun Bt h1 h2 => hb Bt h1 (OnLambda.toT h2)⟩

/-- **SUPERSEDED IN r5 (S75): see `ZT5A.P428Genuine8` (r6; the r5 `P428Genuine5` was BROKEN, `statement_audit_r5_opus`).**  (r4 text follows.) **THE GENUINE CLAIM (volume-uniform strong reading).**  Statement parameters
`(ell, M, R, F, a)` are fixed FIRST (`2 ≤ ell`, `0 < M`, `10 ≤ F` the cube-size cap, `F + 2 ≤ R`,
`0 < a` the mass constant of (3.16)/(3.24)); then `a₀ > 0` (the smallness threshold of
"`M α₀` sufficiently small", p.396/p.428), then `γ₀ > 0`; then everything else: `k`, the unit torus
`Lu`, `α₀` with `F M α₀ ≤ a₀`, the tower, `Λ`, `U`, `B̃`.  `a₀` may depend on `(ell,M,R,F,a)`;
`γ₀` may depend on those and on `a₀` but NOT on `k, Lu, α₀, S, Λ, U, B̃`.  There is NO ingredient
family in the signature: the ingredients are the genuine ones (`GenP.genForm`, `GenP.genC`). -/
def P428Genuine (ell M R F : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R ∧ 0 < a) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * M * α₀ ≤ a₀ →
      CoercGenAt ell M R k hell a Lu F α₀ γ₀

/-- **PRINT variant**: the printed sentence only says "`γ₀ > 0` independent of `k` and `U`", so `γ₀`
may depend on the unit torus `Lu` (volume). -/
def P428GenuinePrint (ell M R F : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R ∧ 0 < a) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Lu : PeriodicLatticeExtent), ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * M * α₀ ≤ a₀ →
        CoercGenAt ell M R k hell a Lu F α₀ γ₀

/-- both-endpoint convention, strong reading -/
def P428GenuineBoth (ell M R F : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R ∧ 0 < a) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * M * α₀ ≤ a₀ →
      CoercGenAtBoth ell M R k hell a Lu F α₀ γ₀

theorem P428Genuine.toPrint {ell M R F : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine ell M R F hell a) : P428GenuinePrint ell M R F hell a := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, fun Lu => ⟨γ₀, hγ, fun k α₀ h1 h2 => h k Lu α₀ h1 h2⟩⟩

/-- the touching-convention claim IMPLIES the both-endpoint claim (the class of `B̃` shrinks) -/
theorem P428Genuine.toBoth {ell M R F : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine ell M R F hell a) : P428GenuineBoth ell M R F hell a := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, γ₀, hγ, fun k Lu α₀ h1 h2 => (h k Lu α₀ h1 h2).toBoth⟩

theorem P428Genuine.pos_params {ell M R F : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine ell M R F hell a) : 2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R ∧ 0 < a := h.1

#print axioms CoercGenAt.toBoth
#print axioms P428Genuine.toPrint
#print axioms P428Genuine.toBoth

end AdalyFormal.StatementLaneG
