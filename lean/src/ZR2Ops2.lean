import R2Ops1
import ZLocOps
import ZLocLocal

/-!
# R2Ops2 -- `Q'*aQ'` (3.24), `G'` (3.25), `W = I − D G' R D*`, `Δ_π` (3.119), `T = R D*` (3.122)
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- `a_j` of (3.24): `a_{j+1} = a a_j/(a L^{-2} + a_j)`, `a_1 = a_0 = a` (tree `ConstantA.aSeq`
indexes `a_1, a_2, …`). -/
noncomputable def ajSeq (a : ℝ) (ell j : ℕ) : ℝ :=
  if j = 0 then a else AdalyFormal.Balaban.ConstantA.aSeq a (ell : ℝ) (j - 1)

open Classical in
/-- `Q'*aQ'` (3.24): `⟨λ, Q'*aQ'λ⟩ = Σ_j a_j Σ_{y∈Λ_j} L^{j(d-2)} |(Q'_j(U)λ)(y)|²` (`d = 3`,
`η`-free body, see R2Ops1 CONVENTION). -/
noncomputable def Qpa (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
    if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) •
      ((ContinuousLinearMap.adjoint (Qlev G U j y)).comp (Qlev G U j y)) else 0

open Classical in
theorem inner_Qpa (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    ⟪f, Qpa G U a f⟫ = ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
      if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ‖Qlev G U j y f‖ ^ 2 else 0 := by
  simp only [Qpa, ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs
  · simp [real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  · simp

open Classical in
theorem Qpa_symm (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f g : SiteL2 L) :
    ⟪Qpa G U a f, g⟫ = ⟪f, Qpa G U a g⟫ := by
  simp only [Qpa, ContinuousLinearMap.sum_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_left,
      real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    try rw [real_inner_comm]
  · simp

/-- `Δ'_a|_{Ω₀} = Ω₀(Δ_U + Q'*aQ')Ω₀` (p.394). -/
noncomputable def DelpA (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  ((siteMask G.Om0).comp (lapFull U + Qpa G U a)).comp (siteMask G.Om0)

/-- `G' = (Δ'_a|_{Ω₀})^{-1}` (p.394): the inverse on `L²(Ω₀)`, extended by `0`.  Realised as
`(Ω₀Δ'_aΩ₀ + (1−Ω₀))⁻¹ Ω₀`: the padding `(1−Ω₀)` is invisible on `L²(Ω₀)`.  When the print's
positivity assertion "Δ'_a is positive" (p.395, no proof given) fails, `Ring.inverse` returns `0`. -/
noncomputable def Gp (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  (Ring.inverse (DelpA G U a + (1 - siteMask G.Om0))).comp (siteMask G.Om0)

/-- `W = I − D G' R D*` (the map in (3.119)). -/
noncomputable def Wop (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  1 - (gradL2 U).comp ((Gp G U a).comp ((Rproj G U).comp (gradAdj U)))

/-- r6: the plaquettes OF `Ω` -- all four boundary bonds of `p` have BOTH endpoints in `Ω`.  **This is the lane's READING of CMP99b p.394**
("They depend on the configuration U restricted to Ω₀"), NOT the printed wording: the print states the Dirichlet sandwich `Ω₀Δ'_aΩ₀` for the site operator
only.  The literal sandwich on the touching bond set and the "all four bonds touch Ω" reading are both false for the statement (r5 collapse; concave-corner
argument, statement_audit_r6_opus attack 2); `plaqIn` is the only surviving reading (paper argument, not Lean). -/
def plaqIn (S : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticePlaquette L) :=
  {p | ∀ e ∈ periodicPlaquetteBoundaryEdges p, e.1 ∈ S ∧ periodicLatticeShift e.1 e.2 ∈ S}

/-- `Δ` of (3.10), `η = 1`, source-normalised `tr`: `D*D + Δ'` with the plaquette sums restricted to `plaqIn Ω₀` (the lane's reading of "depend on U restricted to
Ω₀", p.394; NOT the printed Dirichlet sandwich; r5 summed over the whole torus). -/
noncomputable def Delta (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (plaqIn G.Om0)

/-- `Δ_π` (3.119): `⟨A,Δ_πA⟩ = ⟨WA, Δ WA⟩`, as the operator `W* Δ W` on all fine bonds. -/
noncomputable def DpiFull (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((Delta G U).comp (Wop G U a))

theorem DpiFull_symm (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFull G U a x, y⟫ = ⟪x, DpiFull G U a y⟫ := by
  simp only [DpiFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _

/-- The printed form (3.119): `⟨A,Δ_πA⟩ = ⟨A − DG'RD*A, Δ(A − DG'RD*A)⟩`. -/
theorem inner_DpiFull (G : TowerGeom L) (U : Cfg L) (a : ℝ) (A : BondFnL2 L) :
    ⟪A, DpiFull G U a A⟫ = ⟪A - gradL2 U (Gp G U a (Rproj G U (gradAdj U A))),
      Delta G U (A - gradL2 U (Gp G U a (Rproj G U (gradAdj U A))))⟫ := by
  simp only [DpiFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, Wop,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]

/-- `T = R D*` (bonds → sites): the gauge-fixing operator of `‖RD*A‖²` in (3.128). -/
noncomputable def Tfull (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] SiteL2 L :=
  (Rproj G U).comp (gradAdj U)

/-- `D R D* = T* T` (needs `R*R = R`, proved): the printed `DRD*` of (3.122) IS `T*T`. -/
theorem Tfull_adj_comp (G : TowerGeom L) (U : Cfg L) :
    (ContinuousLinearMap.adjoint (Tfull G U)).comp (Tfull G U)
      = (gradL2 U).comp ((Rproj G U).comp (gradAdj U)) := by
  have h1 : ContinuousLinearMap.adjoint (Tfull G U)
      = (gradL2 U).comp (ContinuousLinearMap.adjoint (Rproj G U)) := by
    simp only [Tfull, ContinuousLinearMap.adjoint_comp, gradAdj, ContinuousLinearMap.adjoint_adjoint]
  rw [h1, Rproj_adjoint]
  ext1 A
  simp only [ContinuousLinearMap.comp_apply, Tfull]
  rw [Rproj_idem]

theorem DelpA_mask_left (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    siteMask G.Om0 (DelpA G U a f) = DelpA G U a f := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_idem]

theorem DelpA_mask_right (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    DelpA G U a (siteMask G.Om0 f) = DelpA G U a f := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_idem]

/-- THE PRINTED `G' = (Δ'_a|_{Ω₀})⁻¹` (p.394): whenever the Dirichlet operator is invertible on
`L²(Ω₀)` (the print's "Δ'_a is positive", p.395), `G' f` is supported in `Ω₀` and
`Ω₀Δ'_aΩ₀ (G' f) = Ω₀ f`. -/
theorem Gp_spec (G : TowerGeom L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (f : SiteL2 L) :
    siteMask G.Om0 (Gp G U a f) = Gp G U a f ∧ DelpA G U a (Gp G U a f) = siteMask G.Om0 f := by
  obtain ⟨u, hu'⟩ := hu
  set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
  have hGp : Gp G U a f = (↑u⁻¹ : SiteL2 L →L[ℝ] SiteL2 L) (siteMask G.Om0 f) := by
    unfold Gp
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hX, ← hu', Ring.inverse_unit]
  set v := Gp G U a f with hv
  have hXv : X v = siteMask G.Om0 f := by
    show X v = _
    rw [hGp, ← hu']
    exact ContinuousLinearMap.ext_iff.mp u.mul_inv _
  have h1 : DelpA G U a v = siteMask G.Om0 f := by
    have h2 := congrArg (siteMask G.Om0) hXv
    have e : siteMask G.Om0 (X v) = DelpA G U a v := by
      rw [hX]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, map_add, map_sub, DelpA_mask_left]
      have : siteMask G.Om0 (siteMask G.Om0 v) = siteMask G.Om0 v := siteMask_idem _ _
      rw [this, sub_self, add_zero]
    rw [e, siteMask_idem] at h2
    exact h2
  refine ⟨?_, h1⟩
  have hx2 : X v = DelpA G U a v + (v - siteMask G.Om0 v) := by
    rw [hX]; rfl
  have h4 : DelpA G U a v + (v - siteMask G.Om0 v) = DelpA G U a v := by
    rw [← hx2, hXv, h1]
  have h3 : v - siteMask G.Om0 v = 0 := add_eq_left.mp h4
  exact (sub_eq_zero.mp h3).symm

#print axioms Gp_spec
#print axioms inner_Qpa
#print axioms Qpa_symm
#print axioms DpiFull_symm
#print axioms inner_DpiFull
#print axioms Tfull_adj_comp

/-! ## r6 pins (R1): `Δ` depends on `U` only on the bonds with both endpoints in `Ω₀`, and annihilates fields off them.
These live in THIS module so that a definitional mutant of `Delta` (e.g. restoring the global plaquette sum) fails here. -/

/-- bonds with BOTH endpoints in `S` (the `CubeBond` convention). -/
def BothIn (S : Set (PeriodicLatticeSite L)) (e : Bond L) : Prop :=
  e.1 ∈ S ∧ periodicLatticeShift e.1 e.2 ∈ S

theorem plaqIn_agree (S : Set (PeriodicLatticeSite L)) {U U' : Cfg L}
    (hUU : ∀ e : Bond L, BothIn S e → U e = U' e) : AdalyFormal.StatementLaneR6.AgreeOn (plaqIn S) U U' :=
  fun _ hp e he => hUU e (hp e he)

/-- **R1 pin.**  `Δ` depends on `U` only on the `Ω₀`-both bonds (CMP99b p.394: "depend on the configuration `U` restricted to `Ω₀`"). -/
theorem Delta_congr_outside (G : TowerGeom L) {U U' : Cfg L}
    (hUU : ∀ e : Bond L, BothIn G.Om0 e → U e = U' e) : Delta G U = Delta G U' := by
  unfold Delta
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_congr (plaqIn_agree _ hUU)

theorem Delta_Om0_univ (G : TowerGeom L) (hG : G.Om0 = Set.univ) (U : Cfg L) :
    Delta G U = AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U := by
  unfold Delta
  have : plaqIn G.Om0 = Set.univ := by
    rw [hG]; ext p; simp [plaqIn]
  rw [this]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_univ U

open AdalyFormal.StatementLaneR6 in
/-- **R1 control (Dirichlet).**  `Δ` annihilates every bond field that vanishes on all `Ω₀`-both bonds. -/
theorem Delta_outside_zero (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L)
    (hA : ∀ e : Bond L, BothIn G.Om0 e → A e = 0) : Delta G U A = 0 := by
  unfold Delta
  refine ext_inner_left ℝ (fun v => ?_)
  rw [inner_deltaKLocCLM, inner_zero_right]
  have hm : plaqMask (plaqIn G.Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A) = 0 := by
    refine PiLp.ext (fun p => ?_)
    rw [plaqMask_apply]
    split_ifs with hp
    · have hx : A = WithLp.toLp 2 (WithLp.ofLp A) := rfl
      rw [hx, AdalyFormal.Balaban.CStarDeltaKCOperator.curlCovariantLM_L2_toLp]
      show AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U (WithLp.ofLp A) p = 0
      unfold AdalyFormal.Balaban.CovariantOperators.curlValueCovariant
      have e1 := hA _ (hp _ ((edge_mem p _).mpr (Or.inl rfl)))
      have e2 := hA _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl))))
      have e3 := hA _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl)))))
      have e4 := hA _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl)))))
      have e1' : (WithLp.ofLp A) (p.1, p.2.1.1) = 0 := e1
      have e2' : (WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0 := e2
      have e3' : (WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 := e3
      have e4' : (WithLp.ofLp A) (p.1, p.2.1.2) = 0 := e4
      rw [e1', e2', e3', e4']
      simp
    · rfl
  have hb : deltaPrimeBilL2NormLoc U (plaqIn G.Om0) v A = 0 := by
    show deltaPrimeBilNormLoc U (plaqIn G.Om0) _ _ = 0
    unfold deltaPrimeBilNormLoc
    have hraw : ∀ (B C : Bond L → SuTwo), (∀ e : Bond L, BothIn G.Om0 e → C e = 0) →
        deltaPrimeBilRawLoc U (plaqIn G.Om0) B C = 0 := by
      intro B C hC
      rw [deltaPrimeBilRawLoc_apply]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      split_ifs with hp
      · exact AdalyFormal.Balaban.DeltaPrimeOperator.bilPlaq_eq_zero_of_right_bonds_zero U p B C
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inl rfl))))
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl)))))
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))))
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))))
      · rfl
    have hraw' : ∀ (B C : Bond L → SuTwo), (∀ e : Bond L, BothIn G.Om0 e → C e = 0) →
        deltaPrimeBilRawLoc U (plaqIn G.Om0) C B = 0 := by
      intro B C hC
      rw [deltaPrimeBilRawLoc_apply]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      split_ifs with hp
      · exact AdalyFormal.Balaban.DeltaPrimeOperator.bilPlaq_eq_zero_of_left_bonds_zero U p C B
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inl rfl))))
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl)))))
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))))
          (hC _ (hp _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))))
      · rfl
    have hAA : ∀ e : Bond L, BothIn G.Om0 e →
        ((AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap A) e = 0 := hA
    have h1 := hraw ((AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap v)
      ((AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap A) hAA
    have h2 := hraw' ((AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap v)
      ((AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap A) hAA
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
    rw [h1, h2]; ring
  rw [hm, hb]
  simp


#print axioms Delta_outside_zero
#print axioms Delta_congr_outside
#print axioms Delta_Om0_univ

end AdalyFormal.IngredientFamilyR2
