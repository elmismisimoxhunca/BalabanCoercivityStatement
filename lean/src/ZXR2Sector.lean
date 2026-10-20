import ZXR2Ops4
import ZLocJet

/-!
# R2Sector (r8: jets LOCAL per component, `ZLocJet`; bridges `QlinB_eq_r7`, `C2rawB_eq_r7`) -- the bond-sector data `Q = (Q_j(U))_j` (3.15)/(3.110) and `C^{(2)}` (3.127) from the
printed raw map, as a `BondSector`

`Q_j(U) = L^{-j}·D(qCompX_j)(0)` (CMP99b (3.14): `Q_j(U,ηA)/(L^jη) = Q_j(U)A + …`, raw variable
`a = ηA`), `C^{(2)}|_{Λ_j} = L^{-j}·½D²(qCompX_j)(0)(a,a)` (η-free body of "`C^{(2)} = L^jη C_j^{(2)}`",
p.421, for the plain `H` of (3.126)); both read at the level-`j` bonds `b ∈ Λ_j`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)

variable {L : PeriodicLatticeExtent}

/-- coordinates of an su(2)-valued bond field. -/
noncomputable def suCoord : BondFnL2 L →ₗ[ℝ] XS L where
  toFun A := fun b => fromM2 ((WithLp.ofLp A b : SuTwo) : M2)
  map_add' A B := by funext b; simp
  map_smul' c A := by funext b; simp

/-- the su(2)-valued bond field of coordinates. -/
noncomputable def suCoordInv : XS L →ₗ[ℝ] BondFnL2 L where
  toFun a := WithLp.toLp 2 (fun b => ⟨toM2 (a b), toM2_mem _⟩)
  map_add' a a' := by
    refine PiLp.ext (fun b => ?_)
    apply Subtype.ext
    simp
  map_smul' c a := by
    refine PiLp.ext (fun b => ?_)
    apply Subtype.ext
    simp

theorem suCoordInv_suCoord (A : BondFnL2 L) : suCoordInv (suCoord A) = A := by
  refine PiLp.ext (fun b => ?_)
  apply Subtype.ext
  show toM2 (fromM2 ((WithLp.ofLp A b : SuTwo) : M2)) = _
  exact toM2_fromM2 (WithLp.ofLp A b).2

theorem suCoord_suCoordInv (a : XS L) : suCoord (suCoordInv a) = a := by
  funext b
  show fromM2 (toM2 (a b)) = a b
  exact fromM2_toM2 _

#print axioms suCoordInv_suCoord
#print axioms suCoord_suCoordInv


/-- `L^j Q_j(U)`: the first-order jet of the level-`j` composite raw map (3.13), as an operator on
the su(2) bond fields. -/
noncomputable def QlinB (G : TowerGeom L) (U : Cfg L) (j : ℕ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    (suCoordInv ∘ₗ ((QlinCompL G.ell (bgTower G U) j : XS L →L[ℝ] XS L) : XS L →ₗ[ℝ] XS L) ∘ₗ suCoord)

theorem QlinB_apply (G : TowerGeom L) (U : Cfg L) (j : ℕ) (A : BondFnL2 L) :
    QlinB G U j A = suCoordInv (QlinCompL G.ell (bgTower G U) j (suCoord A)) := rfl

/-- r8 BRIDGE: on a regular background tower the repaired `QlinB` is the r7 `QlinB` (jet of the whole composite). -/
theorem QlinB_eq_r7 (G : TowerGeom L) (U : Cfg L) (J : ℕ) (hreg : RegTower G.ell (bgTower G U) J) (j : ℕ) (hj : j ≤ J)
    (A : BondFnL2 L) : QlinB G U j A = suCoordInv (QlinCompX G.ell (bgTower G U) j (suCoord A)) := by
  rw [QlinB_apply, QlinCompL_eq_QlinCompX G.ell (bgTower G U) J hreg j hj]

theorem QlinB_zero (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) : QlinB G U 0 A = A := by
  rw [QlinB_apply, QlinCompL_zero, ContinuousLinearMap.id_apply, suCoordInv_suCoord]

/-- the second derivative `D²(qCompX_j)(0)` as a bilinear map on su(2) bond fields. -/
noncomputable def D2B (G : TowerGeom L) (U : Cfg L) (j : ℕ) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  LinearMap.mk₂ ℝ
    (fun A B => suCoordInv (D2CompL G.ell (bgTower G U) j (suCoord A) (suCoord B)))
    (fun A A' B => by simp)
    (fun c A B => by simp)
    (fun A B B' => by simp)
    (fun c A B => by simp)

/-- `C_j^{raw}(A) = ½ D²(qCompX_j)(0)(A,A)`. -/
noncomputable def C2rawB (G : TowerGeom L) (U : Cfg L) (j : ℕ) (A : BondFnL2 L) : BondFnL2 L :=
  (1 / 2 : ℝ) • D2B G U j A A

theorem C2rawB_eq (G : TowerGeom L) (U : Cfg L) (j : ℕ) (A : BondFnL2 L) :
    C2rawB G U j A = suCoordInv (C2CompL G.ell (bgTower G U) j (suCoord A)) := by
  unfold C2rawB C2CompL D2B
  simp

/-- r8 BRIDGE (second order): on a regular tower `C2rawB` is the r7 one (`C2CompX`, second `fderiv` of the whole composite). -/
theorem C2rawB_eq_r7 (G : TowerGeom L) (U : Cfg L) (J : ℕ) (hreg : RegTower G.ell (bgTower G U) J) (j : ℕ) (hj : j ≤ J)
    (A : BondFnL2 L) : C2rawB G U j A = suCoordInv (C2CompX G.ell (bgTower G U) j (suCoord A)) := by
  rw [C2rawB_eq, C2CompL_eq_C2CompX G.ell (bgTower G U) J hreg j hj]

/-- `Q = (Q_j(U))_j` on `𝔅`: `(QA)(j,b) = L^{-j} (L^jQ_j A)(b)`. -/
noncomputable def QfullOf (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] FSp G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2 (fun p : BIdx G =>
        (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1)
      map_add' := fun A A' => by
        refine PiLp.ext (fun p => ?_); simp [smul_add]
      map_smul' := fun c A => by
        refine PiLp.ext (fun p => ?_)
        simp only [map_smul, PiLp.smul_apply, RingHom.id_apply, WithLp.ofLp_toLp]
        exact smul_comm _ _ _ }

/-- `C^{(2)}` on `𝔅`: `C^{(2)}(A)(j,b) = L^{-j} (C_j^{raw}(A))(b)`. -/
noncomputable def C2fullOf (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) : FSp G :=
  WithLp.toLp 2 (fun p : BIdx G =>
    (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1)

theorem C2fullOf_quad (G : TowerGeom L) (U : Cfg L) : IsQuadMap (C2fullOf G U) := by
  refine ⟨LinearMap.mk₂ ℝ
    (fun A B => WithLp.toLp 2 (fun p : BIdx G =>
      (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp ((1 / 2 : ℝ) • D2B G U p.1 A B)) p.2.1))
    (fun A A' B => by refine PiLp.ext (fun p => ?_); simp [smul_add])
    (fun c A B => by
      refine PiLp.ext (fun p => ?_); simp only [map_smul, LinearMap.smul_apply, PiLp.smul_apply]
      simp only [smul_smul]; congr 1; ring)
    (fun A B B' => by refine PiLp.ext (fun p => ?_); simp [smul_add])
    (fun c A B => by
      refine PiLp.ext (fun p => ?_); simp only [map_smul, PiLp.smul_apply]
      simp only [smul_smul]; congr 1; ring), fun A => ?_⟩
  refine PiLp.ext (fun p => ?_)
  simp [C2fullOf, C2rawB]

/-- THE BOND SECTOR OF THE PRINT, assembled from the printed raw map. -/
noncomputable def bondSectorOf (G : TowerGeom L) (U : Cfg L) : BondSector G where
  Qfull := QfullOf G U
  C2full := C2fullOf G U
  C2_quad := C2fullOf_quad G U

#print axioms QlinB_eq_r7
#print axioms C2rawB_eq_r7
#print axioms C2fullOf_quad
#print axioms bondSectorOf

end AdalyFormal.IngredientFamilyR2
