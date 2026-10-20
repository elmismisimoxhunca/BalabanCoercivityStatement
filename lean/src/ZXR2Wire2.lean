import ZXR2Wire1
import ZLocJ
import ZLocLocal

/-!
# R2Wire2 -- `IngrB_genuine : Ingr ell Lu (scaleUp ell k Lu) Lam` from the printed operators
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2 su2LogExp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower LamPrime IsDroppedIn Ingr OnLambdaTildeIn OnLambda)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

/-- the parameters of the family (printed: `L`, `k`, `{Ω_j}`, `U`, `a`, `Λ`). -/
structure IngrBParams where
  ell : ℕ
  k : ℕ
  Lu : PeriodicLatticeExtent
  hell : 0 < ell
  S : Tower (scaleUp ell k Lu)
  U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)
  a : ℝ
  Lam : Set (PeriodicLatticeSite Lu)

namespace IngrBParams
variable (P : IngrBParams)

abbrev Lf : PeriodicLatticeExtent := scaleUp P.ell P.k P.Lu
noncomputable abbrev G : TowerGeom (scaleUp P.ell P.k P.Lu) := geomOf P.ell P.k P.S
/-- `η = L^{-k}`. -/
noncomputable def eta : ℝ := ((P.ell : ℝ) ^ P.k)⁻¹

theorem eta_pos : 0 < P.eta := by
  unfold eta
  have : (0 : ℝ) < P.ell := by exact_mod_cast P.hell
  positivity

noncomputable def sector : BondSector P.G := bondSectorOf P.G P.U
/-- `J` of (3.11) (the unit-spacing body: `η^d · J_pw`, see R2Ops1 CONVENTION), in the su(2) chart of
THIS lane: `V₁ = exp(a)`, i.e. `a = iA_h` (`A_h` the Hermitian field of the print, `U' = e^{iA_h}`), so
`J_su2 = i·J_h`.  r1's `JSU2 = (−i)η⁻³ Jfield` is the image under the OPPOSITE chart `a = −iA_h`
(its `J_pairing`: `hsInner a (JSU2 b) = tr((i a) J_h)`), hence the sign: `J_su2 = −JSU2`.
(`⟨H C^{(2)}(a), J⟩` is invariant only if the chart of `C^{(2)}` and of `J` agree; `C^{(2)}` is even in `a`
and flips sign with the chart, `J` flips sign too.) -/
noncomputable def Jf : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) P.U b))

noncomputable def data : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  baseData P.G P.U P.a P.sector P.Jf

theorem data_laws : P.data.Laws := baseData_laws P.G P.U P.a P.sector P.Jf

/-- THE operator `G₁⁻¹` of (3.128): the unique symmetric operator with the printed form
(exists by `exists_G1inv`; `Classical.choose` is harmless: uniqueness `G1inv_unique`). -/
noncomputable def G1inv : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  Classical.choose (P.data.exists_G1inv P.data_laws)

theorem G1inv_spec : P.data.IsG1inv P.G1inv := Classical.choose_spec (P.data.exists_G1inv P.data_laws)

/-- unit-torus background `Ū^k`. -/
noncomputable def unitBgU : PeriodicLinkConfiguration SU2 P.Lu :=
  unitBg P.ell P.k P.Lu P.hell (bgTower P.G P.U P.k)

/-- `Q₁` (unit → coarse, printed one-step linear part at the unit level). -/
noncomputable def Q1 : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo) :=
  Q1jet P.ell P.unitBgU

noncomputable def tau : FSp P.G →L[ℝ] BondFnL2 P.Lu := tauExt P.ell P.k P.Lu P.hell P.S

/-- `Q` of the statement carriers: top-level `Q_k(U)`, fine → unit bonds. -/
noncomputable def Qin : BondFnL2 (scaleUp P.ell P.k P.Lu) →L[ℝ] BondFnL2 P.Lu :=
  P.tau.comp P.sector.Qfull

/-- `G₁` (Ingr normalisation): `η⁻¹ · ι G₁ ι*` (Riesz representative, in the unweighted structure, of
the η-weighted covariance; `ι = E₀ ↪ bonds`). -/
noncomputable def G1in : BondFnL2 (scaleUp P.ell P.k P.Lu) →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (P.eta⁻¹) • (iE P.G).comp ((P.data.G1 P.G1inv).comp (pE P.G))

/-- `H₁ = ι G₁Q*(QG₁Q*)⁻¹ τ*` acting on unit-bond fields (zero-extended to `𝔅`). -/
noncomputable def H1in : BondFnL2 P.Lu →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (iE P.G).comp ((P.data.H1 P.G1inv).comp (ContinuousLinearMap.adjoint P.tau))

/-- `D̃⁽²⁾(B) = h C̃⁽²⁾(B)`, `h = L⁻¹ ι_D H₀⁻¹ ρ` (CMP109 p.267; `LQ̃h = I`). -/
noncomputable def D2in (B : BondFnL2 P.Lu) : BondFnL2 P.Lu :=
  WithLp.toLp 2 (((P.ell : ℝ)⁻¹) • hLift P.Lam P.Q1 (C2tilde P.ell P.unitBgU (WithLp.ofLp B)))

theorem D2in_quad (c : ℝ) (B : BondFnL2 P.Lu) : P.D2in (c • B) = c ^ 2 • P.D2in B := by
  unfold D2in
  have h1 : C2tilde P.ell P.unitBgU (c • WithLp.ofLp B) = c ^ 2 • C2tilde P.ell P.unitBgU (WithLp.ofLp B) :=
    C2tilde_smul P.ell P.unitBgU c (WithLp.ofLp B)
  rw [show WithLp.ofLp (c • B) = c • WithLp.ofLp B from rfl, h1, map_smul]
  refine PiLp.ext (fun e => ?_)
  simp only [PiLp.smul_apply, Pi.smul_apply, WithLp.ofLp_toLp]
  rw [smul_comm]

#print axioms D2in_quad

/-- THE GENUINE INGREDIENT FAMILY, one `(S,U)`: every field of `Ingr` is built from the printed
operators.  Hypotheses (named, NOT assumed by the final statement): `hb` = the coupled constraint
matrix `H₀` of (3.157) is bijective (`C`, `h` exist); `hunit` = `(Q G₁ Q*)` invertible (the print
writes `(QG₁Q*)⁻¹`), which `unit_of_chain` derives from coercivity of (3.128). -/
noncomputable def toIngr (hb : Function.Bijective (H0 P.Lam P.Q1))
    (hunit : IsUnit ((P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin))) :
    Ingr P.ell P.Lu (scaleUp P.ell P.k P.Lu) P.Lam where
  Q := P.Qin
  Qs := ContinuousLinearMap.adjoint P.Qin
  G1 := P.G1in
  a := P.a
  H1 := P.H1in
  D2 := P.D2in
  J := P.Jf
  Q1 := P.Q1
  C := Cop P.Lam P.Q1
  Qs_adj := fun x y => by rw [ContinuousLinearMap.adjoint_inner_right]
  D2_quad := P.D2in_quad
  QGQ_unit := hunit
  C_id := fun B b hb' => Cop_id P.Lam P.Q1 B b hb'
  C_ker := fun B _ _ c hc => Cop_ker P.Lam P.Q1 hb B c hc


theorem tau_adjoint_bijective (hτ : Function.Bijective P.tau) :
    Function.Bijective (ContinuousLinearMap.adjoint P.tau) := by
  have hinj : Function.Injective (ContinuousLinearMap.adjoint P.tau) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := hτ.2 x
    have : ⟪P.tau y, P.tau y⟫ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hx, inner_zero_right]
    have h0 : P.tau y = 0 := inner_self_eq_zero.mp this
    rw [h0]
  refine ⟨hinj, ?_⟩
  have hrank : Module.finrank ℝ (BondFnL2 P.Lu) = Module.finrank ℝ (FSp P.G) :=
    (LinearEquiv.ofBijective (P.tau : FSp P.G →ₗ[ℝ] BondFnL2 P.Lu) hτ).finrank_eq.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (ContinuousLinearMap.adjoint P.tau : BondFnL2 P.Lu →ₗ[ℝ] FSp P.G)) hrank).mp hinj

/-- `hunit` from the printed chain: `G⁻¹` coercive (positive-definiteness of `Δ_a`-type operators,
p.395/Thm 3.1), `‖Δ^{(2)}‖ ≤ ε < c` (the smallness (3.137)), `Q*` injective, and `τ` bijective
(the full-support case). -/
theorem unit_of_chain (hτ : Function.Bijective P.tau) {c ε : ℝ} (hcε : ε < c)
    (hc : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, P.data.Ginv x⟫) (hε : ‖P.data.Delta2 P.data_laws‖ ≤ ε)
    (hQs : Function.Injective P.data.Qs) (hη : 0 < P.eta) :
    IsUnit ((P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin)) := by
  have hM := P.data.QG1Qs_isUnit_of_small P.data_laws P.G1inv_spec hcε hc hε hQs
  have heq : (P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin)
      = (P.eta⁻¹) • (P.tau.comp (((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs).comp
          (ContinuousLinearMap.adjoint P.tau))) := by
    have hQs' : P.data.Qs = (pE P.G).comp (ContinuousLinearMap.adjoint P.sector.Qfull) := by
      show ContinuousLinearMap.adjoint (P.sector.Qfull.comp (iE P.G)) = _
      rw [ContinuousLinearMap.adjoint_comp]; rfl
    have hQ' : P.data.Q = P.sector.Qfull.comp (iE P.G) := rfl
    ext1 x
    simp only [Qin, G1in, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.smul_apply, hQs', hQ', map_smul]
  rw [heq]
  have hτa := P.tau_adjoint_bijective hτ
  have hMb : Function.Bijective ((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs) :=
    (ContinuousLinearMap.isUnit_iff_bijective).mp hM
  have hcomp : Function.Bijective (P.tau.comp (((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs).comp
          (ContinuousLinearMap.adjoint P.tau))) := by
    show Function.Bijective (P.tau ∘ ((P.data.Q.comp (P.data.G1 P.G1inv)).comp P.data.Qs) ∘
      ⇑(ContinuousLinearMap.adjoint P.tau))
    exact hτ.comp (hMb.comp hτa)
  refine (ContinuousLinearMap.isUnit_iff_bijective).mpr ?_
  have hne : P.eta⁻¹ ≠ 0 := inv_ne_zero hη.ne'
  have hs : Function.Bijective (fun y : BondFnL2 P.Lu => P.eta⁻¹ • y) :=
    ⟨fun a b h => by simpa [smul_right_inj hne] using h, fun y => ⟨P.eta • y, by simp [smul_smul, hη.ne']⟩⟩
  exact hs.comp hcomp

end IngrBParams

/-- **R1 pin (J).**  `J` of (3.11) depends on `U` only on the `Ω₀`-both bonds (lane reading of p.394 "depend on U restricted to Ω₀"; not the printed wording).
Lives here so a mutant restoring the global plaquette sum in `Jf` fails in THIS module. -/
theorem Jf_congr_outside (P : IngrBParams)
    (U' : PeriodicLinkConfiguration SU2 (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn P.G.Om0 e → P.U e = U' e) :
    ({ P with U := U' } : IngrBParams).Jf = P.Jf := by
  unfold IngrBParams.Jf
  have h := AdalyFormal.IngredientFamily.JSU2Loc_congr (η := 1) (plaqIn_agree _ hUU)
  show WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) U' b))
    = WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) P.U b))
  rw [h]

#print axioms Jf_congr_outside

end AdalyFormal.IngredientFamilyR2
