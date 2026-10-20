import ZR2B8
import IngredientG1H1
import ZIngredientJ
import IngredientD2

/-!
# R2C1 -- ingredient-class `IngrB`: what every genuine ingredient family must satisfy (CMP99b (3.156)).
Imports (read-only) the ingredient-family lane's `BaseData`, `JSU2`, `D2unit`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.IngredientFamily (BaseData JSU2 D2unit)

/-- the coarse-site embedding `y ↦ ell^k · y` of the unit torus into the fine torus -/
def embSite (ell : ℕ) (hell : 0 < ell) (k : ℕ) {Lu : PeriodicLatticeExtent}
    (y : PeriodicLatticeSite Lu) : PeriodicLatticeSite (scaleUp ell k Lu) :=
  fun μ => ⟨ell ^ k * (y μ).val, by
    have hpos : 0 < ell ^ k := pow_pos hell k
    have h1 := (y μ).isLt
    simp only [scaleUp]
    have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : ell ^ k * (y μ).val < (Lu μ + 1) * ell ^ k := by nlinarith
    omega⟩

theorem embSite_mem (ell : ℕ) (hell : 0 < ell) (k : ℕ) {Lu : PeriodicLatticeExtent}
    (y : PeriodicLatticeSite Lu) :
    embSite ell hell k y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
  rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice]
  intro μ
  simp [embSite]

end AdalyFormal.StatementLane2
