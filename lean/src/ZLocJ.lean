import ZIngredientJ

/-!
# ZLocJ -- `J = D* η⁻² Im ∂U` of CMP99b (3.11) with the plaquette function `Im ∂U` restricted to a plaquette set `P`
[r6 statement lane]  The r5 `JSU2` read `U(∂p)` for every plaquette of the torus; (3.11) is a quantity of the operators
"defined by using Dirichlet boundary conditions on Ω₀" (CMP99b p.394), so (the lane's READING, not printed wording) only the plaquettes of `Ω₀` carry `Im ∂U`.
`JSU2Loc η U univ = JSU2 η U` (theorem `JSU2Loc_univ`): a restriction, equal to r5 when `P` is everything.
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamily

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SourceJ AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessY)
open Classical

variable {L : PeriodicLatticeExtent}

/-- `F_{νμ}` of (3.9) with `F := π ∘ Im ∂U` zeroed off the plaquette set `P`. -/
noncomputable def FnuMuLoc (P : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) : Matrix (Fin 2) (Fin 2) ℂ :=
  if hlt : ν < μ then
    (if (y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) ∈ P then
      piProj (imHolonomy U (y, ⟨(ν, μ), hlt⟩)) else 0)
  else if hgt : μ < ν then
    (if (y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) ∈ P then
      -piProj (imHolonomy U (y, ⟨(μ, ν), hgt⟩)) else 0)
  else 0

theorem FnuMuLoc_univ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMuLoc (Set.univ : Set (PeriodicLatticePlaquette L)) U ν μ y = FnuMu U ν μ y := by
  unfold FnuMuLoc FnuMu
  split_ifs <;> simp_all

theorem FnuMuLoc_HT (P : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) : HTm (FnuMuLoc P U ν μ y) := by
  unfold FnuMuLoc
  split_ifs
  · exact piProj_HT (imHolonomy_herm _ _)
  · exact HTm_zero
  · exact HTm_neg (piProj_HT (imHolonomy_herm _ _))
  · exact HTm_zero
  · exact HTm_zero

/-- `J(x,μ) = Σ_{ν≠μ} (D*_ν F^P_{νμ})(x)`. -/
noncomputable def JfieldLoc (P : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ ν : Fin 3, if ν = μ then 0 else DstarDir U ν (fun y => FnuMuLoc P U ν μ y) x

theorem JfieldLoc_univ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    JfieldLoc (Set.univ : Set (PeriodicLatticePlaquette L)) U x μ = Jfield U x μ := by
  unfold JfieldLoc Jfield
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [FnuMuLoc_univ]

theorem JfieldLoc_HT (P : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : HTm (JfieldLoc P U x μ) := by
  unfold JfieldLoc
  refine HTm_sum _ _ fun ν _ => ?_
  split_ifs
  · exact HTm_zero
  · exact DstarDir_HT U ν _ (fun y => FnuMuLoc_HT P U ν μ y) x

/-- localised `J` on the anti-Hermitian `𝔰𝔲(2)` carrier, mesh `η`. -/
noncomputable def JSU2Loc (η : ℝ) (P : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Bond L → SuTwo := fun b =>
  ⟨((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P U b.1 b.2, by
    have h := JfieldLoc_HT P U b.1 b.2
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_smul, h.1, ← neg_smul]
      congr 1
      simp [star_mul']
    · rw [trace_smul, h.2, smul_zero]⟩

theorem JSU2Loc_univ (η : ℝ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    JSU2Loc η (Set.univ : Set (PeriodicLatticePlaquette L)) U = JSU2 η U := by
  funext b
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc Set.univ U b.1 b.2
    = ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield U b.1 b.2
  rw [JfieldLoc_univ]

theorem FnuMuLoc_trivialU (P : Set (PeriodicLatticePlaquette L)) (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMuLoc P (trivialU (L := L)) ν μ y = 0 := by
  unfold FnuMuLoc
  split_ifs
  · rw [imHolonomy_trivialU]; unfold piProj; simp
  · rfl
  · rw [imHolonomy_trivialU]; unfold piProj; simp
  · rfl
  · rfl

theorem JfieldLoc_trivialU (P : Set (PeriodicLatticePlaquette L)) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    JfieldLoc P (trivialU (L := L)) x μ = 0 := by
  unfold JfieldLoc
  apply Finset.sum_eq_zero
  intro ν _
  split_ifs with h
  · rfl
  · exact DstarDir_trivialU_eq_zero_of_G_zero ν _ (fun y => FnuMuLoc_trivialU P ν μ y) x

/-- control: at the flat background the localised `J` vanishes. -/
theorem JSU2Loc_trivial (η : ℝ) (P : Set (PeriodicLatticePlaquette L)) (b : Bond L) :
    JSU2Loc η P (trivialU (L := L)) b = 0 := by
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P trivialU b.1 b.2 = 0
  rw [JfieldLoc_trivialU, smul_zero]

#print axioms JSU2Loc_trivial

#print axioms FnuMuLoc_univ
#print axioms JfieldLoc_HT
#print axioms JfieldLoc_univ
#print axioms JSU2Loc
#print axioms JSU2Loc_univ

end AdalyFormal.IngredientFamily
