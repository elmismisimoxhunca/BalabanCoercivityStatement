import ZLocOps
import ZLocJ

/-!
# ZLocLocal -- LOCALITY of the Dirichlet-localised `Δ` and `J` (r6 R1 must-fire content)
CMP99b p.394: "The operators with the boundary conditions ... depend on the configuration `U` restricted to `Ω₀`."
`Delta_loc_congr`: if `U, U'` agree on every boundary bond of every plaquette of `P`, then `deltaKLocCLM U P = deltaKLocCLM U' P`.
`JSU2Loc_congr`: the same for the localised `J`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.StatementLaneR6

open scoped RealInnerProductSpace
open Classical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (bilinToOperatorBond inner_bilinToOperatorBond
  curlAdjoint dstarDLM dstarDCLM inner_curlAdjoint_right)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (curlCovariantLM_L2_toLp)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator

variable {L : PeriodicLatticeExtent}

/-- `U` and `U'` agree on every boundary bond of every plaquette of `P`. -/
def AgreeOn (P : Set (PeriodicLatticePlaquette L))
    (U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ p ∈ P, ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e

theorem edge_mem (p : PeriodicLatticePlaquette L) (e : PeriodicLatticeEdge L) :
    e ∈ periodicPlaquetteBoundaryEdges p ↔
      (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
        e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
  simp [periodicPlaquetteBoundaryEdges]

section congr
variable {U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
  {p : PeriodicLatticePlaquette L}

theorem edges_eq (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) :
    U (p.1, p.2.1.1) = U' (p.1, p.2.1.1) ∧ U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = U' (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∧
    U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = U' (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∧
    U (p.1, p.2.1.2) = U' (p.1, p.2.1.2) :=
  ⟨h _ ((edge_mem p _).mpr (Or.inl rfl)), h _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl))),
   h _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl)))), h _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))⟩

theorem holonomy_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) :
    periodicPlaquetteHolonomy U p = periodicPlaquetteHolonomy U' p := by
  obtain ⟨h1, h2, h3, h4⟩ := edges_eq h
  unfold periodicPlaquetteHolonomy
  simp only [h1, h2, h3, h4]

theorem holonomyElem_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) :
    holonomyElem U p = holonomyElem U' p := holonomy_congr h

theorem reHolonomy_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) :
    reHolonomy U p = reHolonomy U' p := by
  unfold reHolonomy holonomyElemInv
  rw [holonomyElem_congr h]

theorem imHolonomy_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) :
    imHolonomy U p = imHolonomy U' p := by
  unfold imHolonomy holonomyElemInv
  rw [holonomyElem_congr h]

theorem curlValue_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) (A : Bond L → SuTwo) :
    curlValueCovariant U A p = curlValueCovariant U' A p := by
  obtain ⟨h1, _, _, h4⟩ := edges_eq h
  unfold curlValueCovariant
  rw [h1, h4]

theorem curlMatLM_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) :
    curlMatLM U p = curlMatLM U' p := by
  refine LinearMap.ext (fun A => ?_)
  rw [curlMatLM_apply, curlMatLM_apply, curlValue_congr h]

theorem a1LM_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) : a1LM U p = a1LM U' p := by
  obtain ⟨_, _, _, h4⟩ := edges_eq h
  unfold a1LM
  rw [h4]

theorem a4LM_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) : a4LM U p = a4LM U' p := by
  obtain ⟨h1, _, _, _⟩ := edges_eq h
  unfold a4LM
  rw [h1]

theorem bilPlaq_congr (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e) : bilPlaq U p = bilPlaq U' p := by
  simp only [bilPlaq, firstBilPlaq, secondBilPlaq, pairBil, b1LM, b4LM, curlMatLM_congr h, a1LM_congr h,
    a4LM_congr h, imHolonomy_congr h, reHolonomy_congr h]

end congr

variable {U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
  {P : Set (PeriodicLatticePlaquette L)}

theorem deltaPrimeBilRawLoc_congr (h : AgreeOn P U U') : deltaPrimeBilRawLoc U P = deltaPrimeBilRawLoc U' P := by
  unfold deltaPrimeBilRawLoc
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with hp
  · exact bilPlaq_congr (h p hp)
  · rfl

theorem deltaPrimeOpLoc_congr (h : AgreeOn P U U') : deltaPrimeOpLoc U P = deltaPrimeOpLoc U' P := by
  unfold deltaPrimeOpLoc deltaPrimeBilL2NormLoc deltaPrimeBilNormLoc
  rw [deltaPrimeBilRawLoc_congr h]

theorem plaqMask_curl_congr (h : AgreeOn P U U') (x : BondFnL2 L) :
    plaqMask P (curlCovariantLM_L2 U x) = plaqMask P (curlCovariantLM_L2 U' x) := by
  refine PiLp.ext (fun p => ?_)
  rw [plaqMask_apply, plaqMask_apply]
  split_ifs with hp
  · have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
    rw [hx, curlCovariantLM_L2_toLp, curlCovariantLM_L2_toLp]
    show curlValueCovariant U (WithLp.ofLp x) p = curlValueCovariant U' (WithLp.ofLp x) p
    exact curlValue_congr (h p hp) _
  · rfl

theorem dstarDLoc_congr (h : AgreeOn P U U') : dstarDLoc U P = dstarDLoc U' P := by
  refine LinearMap.ext (fun y => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [inner_dstarDLoc, inner_dstarDLoc, plaqMask_curl_congr h, plaqMask_curl_congr h]

/-- **`Δ_loc` depends only on `U` on the boundary bonds of the plaquettes of `P`** (p.394: "depend on the configuration `U`
restricted to `Ω₀`"). -/
theorem deltaKLocCLM_congr (h : AgreeOn P U U') : deltaKLocCLM U P = deltaKLocCLM U' P := by
  unfold deltaKLocCLM
  rw [dstarDLoc_congr h, deltaPrimeOpLoc_congr h]

#print axioms bilPlaq_congr
#print axioms dstarDLoc_congr
#print axioms deltaKLocCLM_congr

end AdalyFormal.StatementLaneR6

namespace AdalyFormal.IngredientFamily

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SourceJ AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessY)
open AdalyFormal.StatementLaneR6 (AgreeOn edge_mem edges_eq imHolonomy_congr)
open Classical

variable {L : PeriodicLatticeExtent}
  {U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
  {P : Set (PeriodicLatticePlaquette L)}

theorem FnuMuLoc_congr (h : AgreeOn P U U') (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMuLoc P U ν μ y = FnuMuLoc P U' ν μ y := by
  unfold FnuMuLoc
  split_ifs with h1 h2 h3 h4
  · rw [imHolonomy_congr (h _ h2)]
  · rfl
  · rw [imHolonomy_congr (h _ h4)]
  · rfl
  · rfl

theorem FnuMuLoc_conj_congr (h : AgreeOn P U U') (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    conjByAmbient (U (y, ν))⁻¹ (FnuMuLoc P U' ν μ y) = conjByAmbient (U' (y, ν))⁻¹ (FnuMuLoc P U' ν μ y) := by
  unfold FnuMuLoc
  split_ifs with h1 h2 h3 h4
  · rw [(h _ h2 (y, ν) ((edge_mem _ _).mpr (Or.inl rfl)))]
  · simp [conjByAmbient_apply]
  · rw [(h _ h4 (y, ν) ((edge_mem _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))))]
  · simp [conjByAmbient_apply]
  · simp [conjByAmbient_apply]

theorem DstarDir_loc_congr (h : AgreeOn P U U') (ν μ : Fin 3) (x : PeriodicLatticeSite L) :
    DstarDir U ν (fun y => FnuMuLoc P U ν μ y) x = DstarDir U' ν (fun y => FnuMuLoc P U' ν μ y) x := by
  unfold DstarDir
  have hF : ∀ y, FnuMuLoc P U ν μ y = FnuMuLoc P U' ν μ y := FnuMuLoc_congr h ν μ
  simp only [hF]
  rw [FnuMuLoc_conj_congr h]

theorem JfieldLoc_congr (h : AgreeOn P U U') (x : PeriodicLatticeSite L) (μ : Fin 3) :
    JfieldLoc P U x μ = JfieldLoc P U' x μ := by
  unfold JfieldLoc
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs
  · rfl
  · exact DstarDir_loc_congr h ν μ x

theorem JSU2Loc_congr (h : AgreeOn P U U') (η : ℝ) : JSU2Loc η P U = JSU2Loc η P U' := by
  funext b
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P U b.1 b.2
    = ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P U' b.1 b.2
  rw [JfieldLoc_congr h]

#print axioms JfieldLoc_congr
#print axioms JSU2Loc_congr

end AdalyFormal.IngredientFamily
