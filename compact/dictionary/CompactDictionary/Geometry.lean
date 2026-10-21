import CompactDictionary.Coordinates
import BalabanCompact.Target
import ZT5A

/-!
Private hypothesis dictionary. The only divisibility premise below is derived
from the existing `TorusOK` in the headline; no headline is strengthened.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace CompactDictionary

open BalabanCompact
open AdalyFormal.Target.ClayStatement

noncomputable section
variable {L : Extent}

/-- Nominal tower structures, preserving every level exactly. -/
def towerEquiv : Tower L ≃ AdalyFormal.StatementLane.Tower L where
  toFun S := ⟨S.Om⟩
  invFun S := ⟨S.Om⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem towerEquiv_Om (S : Tower L) : (towerEquiv S).Om = S.Om := rfl

theorem shift_eq (x : Site L) (μ : Fin 3) : shift x μ = periodicLatticeShift x μ := rfl

theorem shiftBack_eq (x : Site L) (μ : Fin 3) : shiftBack x μ =
    AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack x μ := rfl

theorem shiftN_eq (x : Site L) (μ : Fin 3) (n : ℕ) :
    shiftN x μ n = AdalyFormal.Balaban.CoarseCurl.coarseShift x n μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [shiftN, ih, AdalyFormal.Balaban.CoarseCurl.coarseShift, Function.iterate_succ_apply', shift_eq]

theorem coarseShift_eq (x : Site L) (s : ℕ) (μ : Fin 3) :
    coarseShift x s μ = AdalyFormal.Balaban.CoarseCurl.coarseShift x s μ := shiftN_eq x μ s

theorem blockOf_eq (y : Site L) (ell : ℕ) : blockOf y ell = AdalyFormal.Balaban.AdmissibleSubspace.blockOf y ell := by
  ext x
  simp [blockOf, AdalyFormal.Balaban.AdmissibleSubspace.blockOf,
    inBlock, AdalyFormal.Balaban.AdmissibleSubspace.inBlock]

theorem coarseLattice_iff (y : Site L) (ell : ℕ) :
    y ∈ CoarseLattice ell ↔ y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L ell := by
  simp [CoarseLattice, AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice]

theorem lamPrime_eq (ell : ℕ) (Lam : Set (Site L)) : LamPrime ell Lam = AdalyFormal.StatementLane.LamPrime ell Lam := by
  ext y
  simp only [LamPrime, AdalyFormal.StatementLane.LamPrime, Set.mem_setOf_eq, coarseLattice_iff, blockOf_eq]

theorem staircasePath_eq (x y : Site L) : staircasePath x y = AdalyFormal.Balaban.AdmissibleSubspace.staircasePath x y := rfl

theorem torusOK_iff (ell M : ℕ) : TorusOK ell M L ↔ AdalyFormal.StatementLane.TorusOK ell M L := Iff.rfl

theorem admissible_iff (ell M R k : ℕ) (S : Tower L) :
    Admissible ell M R k S ↔ AdalyFormal.StatementLane.Admissible ell M R k (towerEquiv S) := Iff.rfl

theorem lambdaOK_iff {Lu : Extent} (ell M R k : ℕ) (S : Tower L) (Lam : Set (Site Lu)) :
    LambdaOK ell M R k S Lam ↔ AdalyFormal.StatementLane.LambdaOK ell M R k (towerEquiv S) Lam := Iff.rfl

theorem lamBlockSum_iff (ell : ℕ) (Lam : Set (Site L)) :
    LamBlockSum ell Lam ↔ AdalyFormal.StatementLaneG.LamBlockSum ell Lam := by
  simp only [LamBlockSum, AdalyFormal.StatementLaneG.LamBlockSum, lamPrime_eq, blockOf_eq]

theorem lambdaOK2_iff {Lu : Extent} (ell M R k : ℕ) (S : Tower L) (Lam : Set (Site Lu)) :
    LambdaOK2 ell M R k S Lam ↔ AdalyFormal.StatementLaneG.LambdaOK2 ell M R k (towerEquiv S) Lam := by
  simp only [LambdaOK2, AdalyFormal.StatementLaneG.LambdaOK2, lambdaOK_iff, lamBlockSum_iff]

theorem classCube_iff (ell M f k : ℕ) (S : Tower L) (sites : Set (Site L)) (j : ℕ) :
    IsClassCube ell M f k S sites j ↔ AdalyFormal.StatementLane.IsClassCube ell M f k (towerEquiv S) sites j := Iff.rfl

theorem cubeBond_iff (sites : Set (Site L)) (b : Bond L) :
    CubeBond sites b ↔ AdalyFormal.StatementLane.CubeBond sites b := Iff.rfl

/-- Both Δ and J use this exact plaquette set, not the touching-bond set. -/
theorem plaqIn_eq (S : Set (Site L)) : plaqIn S = AdalyFormal.IngredientFamilyR2.plaqIn S := rfl

theorem perCubeRegular_iff (ell M f k : ℕ) (S : Tower L) (α η : ℝ) (U : Cfg L) :
    PerCubeRegular ell M f k S α η U ↔ AdalyFormal.StatementLane2.PerCubeRegular2 ell M f k (towerEquiv S) α η U := by
  unfold PerCubeRegular AdalyFormal.StatementLane2.PerCubeRegular2
  simp only [pow_one]
  rfl

theorem covers_iff (ell M c k : ℕ) (S : Tower L) :
    CoversOm0p ell M c k S ↔ AdalyFormal.StatementLane2.CoversOm0p ell M c k (towerEquiv S) := Iff.rfl

/-- Exact constants and gauges: no Frobenius rescaling of the class. -/
theorem classCoupled_iff (ell M c k : ℕ) (S : Tower L) (α η : ℝ) (U : Cfg L) :
    ClassCoupled ell M c k S α η U ↔ AdalyFormal.StatementLane2.ClassCoupled ell M c k (towerEquiv S) α η U := by
  exact and_congr (covers_iff ell M c k S) (perCubeRegular_iff ell M c k S α η U)

theorem sidePow_iff (ell M : ℕ) (a : ℝ) : SidePow ell M a ↔ AdalyFormal.StatementLaneG.SidePow6 ell M a := Iff.rfl

/-- A frozen coarse bond packages the coarse-base proof in its first component. -/
def coarseBondEquiv (ell : ℕ) : CoarseBond (L := L) ell ≃
    AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell where
  toFun c := (⟨c.1.1, (coarseLattice_iff _ _).mp c.2⟩, c.1.2)
  invFun c := ⟨(c.1.1, c.2), (coarseLattice_iff _ _).mpr c.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem crowIn_iff (ell : ℕ) (Lam : Set (Site L)) (c : CoarseBond (L := L) ell) :
    CRowIn ell Lam c.1 ↔ AdalyFormal.StatementLane.CRowIn ell Lam (coarseBondEquiv ell c) := by
  simp only [CRowIn, AdalyFormal.StatementLane.CRowIn, lamPrime_eq, coarseShift_eq, coarseBondEquiv,
    Equiv.coe_fn_mk]

theorem droppedBond_eq (ell : ℕ) (c : CoarseBond (L := L) ell) :
    droppedBond ell c.1 = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell (coarseBondEquiv ell c) := by
  unfold droppedBond pathSite AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast
    AdalyFormal.Balaban.QOne.pathSite
  rw [shiftN_eq]
  rfl

/-- Divisibility is essential to infer a coarse base from a coarse shifted endpoint. -/
theorem coarse_of_coarseShift {ell : ℕ} (hdiv : ∀ μ, ell ∣ L μ + 1)
    (x : Site L) (μ : Fin 3) (h : coarseShift x ell μ ∈ CoarseLattice ell) :
    x ∈ CoarseLattice ell := by
  intro ν
  change ∀ ν, (coarseShift x ell μ ν).val % ell = 0 at h
  have hh := Nat.dvd_of_mod_eq_zero (h ν)
  rw [coarseShift_eq] at hh
  by_cases hν : ν = μ
  · subst ν
    rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq] at hh
    exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_left (dvd_refl ell)).mp
      ((Nat.dvd_mod_iff (hdiv μ)).mp hh))
  · rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne x ell μ ν hν] at hh
    exact Nat.mod_eq_zero_of_dvd hh

theorem isDroppedIn_iff (ell : ℕ) (Lam : Set (Site L)) (b : Bond L)
    (hdiv : ∀ μ, ell ∣ L μ + 1) :
    IsDroppedIn Lam ell b ↔ AdalyFormal.StatementLane.IsDroppedIn Lam ell b := by
  constructor
  · rintro ⟨c, hc, hb⟩
    have hcoarse : c.1 ∈ CoarseLattice ell := by
      rcases hc with h | h
      · exact h.1
      · exact coarse_of_coarseShift hdiv c.1 c.2 h.1
    let c' : CoarseBond (L := L) ell := ⟨c, hcoarse⟩
    exact ⟨coarseBondEquiv ell c', (crowIn_iff ell Lam c').mp hc,
      hb.trans (droppedBond_eq ell c')⟩
  · rintro ⟨c, hc, hb⟩
    let c' := (coarseBondEquiv (L := L) ell).symm c
    refine ⟨c'.1, (crowIn_iff ell Lam c').mpr ?_, ?_⟩
    · simpa [c'] using hc
    · simpa [c'] using hb.trans (droppedBond_eq ell c').symm

@[simp] theorem pauli_eq_zero_iff (v : Vec) : pauli v = 0 ↔ v = 0 := by
  rw [← pauli.map_zero]
  exact pauli.injective.eq_iff

theorem onLambdaT_iff (Lam : Set (Site L)) (B : Bond L → Vec) :
    OnLambdaT Lam B ↔ AdalyFormal.StatementLane2.OnLambdaT Lam (fun b => pauli (B b)) := by
  simp only [OnLambdaT, AdalyFormal.StatementLane2.OnLambdaT, shift_eq, pauli_eq_zero_iff]

theorem onLambdaTildeIn_iff (ell : ℕ) (Lam : Set (Site L)) (B : Bond L → Vec)
    (hdiv : ∀ μ, ell ∣ L μ + 1) :
    OnLambdaTildeIn Lam ell B ↔ AdalyFormal.StatementLane.OnLambdaTildeIn Lam ell (fun b => pauli (B b)) := by
  simp only [OnLambdaTildeIn, AdalyFormal.StatementLane.OnLambdaTildeIn, lamPrime_eq, blockOf_eq, staircasePath_eq,
    isDroppedIn_iff ell Lam _ hdiv, pauli_eq_zero_iff]

theorem bondEnergy_eq (B : Bond L → Vec) : bondEnergy B =
    AdalyFormal.Balaban.RegularUPerturbation.bondEnergy (fun b => pauli (B b)) := by
  simp only [bondEnergy, AdalyFormal.Balaban.RegularUPerturbation.bondEnergy, pauli.norm_map]

end
end CompactDictionary
