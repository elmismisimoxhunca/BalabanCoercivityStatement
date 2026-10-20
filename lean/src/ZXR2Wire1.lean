import ZXR2Unit2
import ZIngredientJ

/-!
# R2Wire1 -- tower geometry from the statement lane's `Tower`, the top-level extraction `τ`
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2 su2LogExp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower LamPrime IsDroppedIn)

/-- `Ω₀`, `Λ_j = Ω_j^{(j)} \ Ω_{j+1}^{(j)}` (p.393) read off the statement lane's tower: level-`j`
coarse sites (coordinates divisible by `ell^j`) in `Ω_j` and not in `Ω_{j+1}`. -/
def geomOf (ell k : ℕ) {Lf : PeriodicLatticeExtent} (S : Tower Lf) : TowerGeom Lf where
  ell := ell
  k := k
  Om0 := S.Om 0
  Lam := fun j => {x | (∀ μ : Fin 3, ell ^ j ∣ (x μ).val) ∧ x ∈ S.Om j ∧ x ∉ S.Om (j + 1)}

/-- the unit bond `(y,μ)` as the level-`k` fine bond `(ell^k y, μ)`. -/
def unitBondEmb (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (e : Bond Lu) :
    Bond (scaleUp ell k Lu) := (embY ell k Lu hell e.1, e.2)

open Classical in
/-- top-level extraction `τ : L²(𝔅) → L²(unit bonds)`: read the level-`k` coordinate at the unit
bond `(y,μ) ↦ (ell^k y, μ)` when it lies in `𝔅`, else `0`. -/
noncomputable def tauExt (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) : FSp (geomOf ell k S) →L[ℝ] BondFnL2 Lu :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun e : Bond Lu =>
        if hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k
        then WithLp.ofLp f ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩ else 0)
      map_add' := fun f g => by
        refine PiLp.ext (fun e => ?_)
        by_cases hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k <;> simp [hb]
      map_smul' := fun r f => by
        refine PiLp.ext (fun e => ?_)
        by_cases hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k <;> simp [hb] }

#print axioms tauExt

end AdalyFormal.IngredientFamilyR2
