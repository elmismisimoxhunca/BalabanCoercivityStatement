import ZR2C2

/-!
# COPY (credited) of compute/statement_lane_20261009_prosecution_claude/src/Junk.lean, namespace changed,
# followed by the R2 must-fire theorems at the end.
# Junk -- PROSECUTION exhibit: P428Faithful ell M R I holds for a CONTENT-FREE ingredient family I
(Q = isometric restriction, G1 = id, a = 0, H1 = 0, D2 = 0, J = 0, Q1 = 0, C = id).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2.JunkCopy

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open scoped RealInnerProductSpace

theorem exists_coisometry (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (h : Module.finrank ℝ E ≤ Module.finrank ℝ F) :
    ∃ (Q : F →L[ℝ] E) (Qs : E →L[ℝ] F),
      (∀ x y, inner ℝ (Q x) y = inner ℝ x (Qs y)) ∧ Q.comp Qs = ContinuousLinearMap.id ℝ E := by
  classical
  let bE := stdOrthonormalBasis ℝ E
  let bF := stdOrthonormalBasis ℝ F
  let ce : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ F) := Fin.castLE h
  have hon : ∀ i j : Fin (Module.finrank ℝ E),
      inner ℝ (bF (ce i)) (bF (ce j)) = if i = j then (1:ℝ) else 0 := by
    intro i j
    have := orthonormal_iff_ite.mp bF.orthonormal (ce i) (ce j)
    simpa [ce, Fin.castLE_inj] using this
  have hQs : ∀ (y : E) (i : Fin (Module.finrank ℝ E)),
      inner ℝ (bF (ce i)) (∑ j, inner ℝ (bE j) y • bF (ce j)) = inner ℝ (bE i) y := by
    intro y i
    simp [inner_sum, inner_smul_right, hon]
  refine ⟨∑ i, (innerSL ℝ (bF (ce i))).smulRight (bE i),
          ∑ i, (innerSL ℝ (bE i)).smulRight (bF (ce i)), ?_, ?_⟩
  · intro x y
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [real_inner_comm, mul_comm]
  · ext y
    simp only [ContinuousLinearMap.comp_apply, sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, ContinuousLinearMap.id_apply]
    simp only [map_sum, map_smul, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hQs]
    exact bE.sum_repr' y


theorem finrank_bondFnL2 (L : PeriodicLatticeExtent) :
    Module.finrank ℝ (BondFnL2 L) = Fintype.card (Bond L) * Module.finrank ℝ SuTwo := by
  rw [(WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem card_bond_le (ell k : ℕ) (hell : 1 ≤ ell) (Lu : PeriodicLatticeExtent) :
    Fintype.card (Bond Lu) ≤ Fintype.card (Bond (scaleUp ell k Lu)) := by
  have hpos : 0 < ell ^ k := pow_pos hell k
  have key : ∀ μ : Fin 3, ∀ v : ℕ, v < Lu μ + 1 → ell ^ k * v < scaleUp ell k Lu μ + 1 := by
    intro μ v hv
    simp only [scaleUp]
    have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : ell ^ k * v < (Lu μ + 1) * ell ^ k := by nlinarith
    omega
  let emb : Bond Lu → Bond (scaleUp ell k Lu) := fun b =>
    (fun μ => ⟨ell ^ k * (b.1 μ).val, key μ _ (b.1 μ).isLt⟩, b.2)
  apply Fintype.card_le_of_injective emb
  intro b b' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun μ => ?_) h2
  have := congrFun h1 μ
  have := congrArg Fin.val this
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hpos this)

theorem finrank_le (ell k : ℕ) (hell : 1 ≤ ell) (Lu : PeriodicLatticeExtent) :
    Module.finrank ℝ (BondFnL2 Lu) ≤ Module.finrank ℝ (BondFnL2 (scaleUp ell k Lu)) := by
  rw [finrank_bondFnL2, finrank_bondFnL2]
  exact Nat.mul_le_mul_right _ (card_bond_le ell k hell Lu)


/-- The CONTENT-FREE ingredient: Q a coisometry, G1 = id, a = 0, H1 = 0, D2 = 0, J = 0, Q1 = 0, C = id. -/
noncomputable def junkIngr (ell : ℕ) (hell : 1 ≤ ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) : Ingr ell Lu (scaleUp ell k Lu) Lam :=
  let h := exists_coisometry (BondFnL2 Lu) (BondFnL2 (scaleUp ell k Lu)) (finrank_le ell k hell Lu)
  { Q := h.choose
    Qs := h.choose_spec.choose
    G1 := ContinuousLinearMap.id ℝ _
    a := 0
    H1 := 0
    D2 := fun _ => 0
    J := 0
    Q1 := 0
    C := LinearMap.id
    Qs_adj := h.choose_spec.choose_spec.1
    D2_quad := by intro c B; simp
    QGQ_unit := by
      have := h.choose_spec.choose_spec.2
      show IsUnit ((h.choose.comp (ContinuousLinearMap.id ℝ _)).comp h.choose_spec.choose)
      rw [ContinuousLinearMap.comp_id, this]
      exact isUnit_one
    C_id := fun _ _ _ => rfl
    C_ker := fun B _ _ c _ => by simp }

theorem form_junk (ell : ℕ) (hell : 1 ≤ ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) (B : BondFnL2 Lu) :
    (junkIngr ell hell k Lu Lam).form B = ‖B‖ ^ 2 := by
  have h := (exists_coisometry (BondFnL2 Lu) (BondFnL2 (scaleUp ell k Lu)) (finrank_le ell k hell Lu)).choose_spec.choose_spec.2
  simp only [Ingr.form, junkIngr, ContinuousLinearMap.comp_id, h, inverse_id,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, zero_mul, sub_zero, ContinuousLinearMap.zero_apply,
    inner_zero_left, inner_zero_right, mul_zero]

/-- **THE EXHIBIT.**  `P428Faithful` holds for the content-free family, for EVERY ell ≥ 2, M > 0, R > 0. -/
theorem junk_satisfies_P428Faithful (ell M R : ℕ) (hell : 2 ≤ ell) (hM : 0 < M) (hR : 0 < R) :
    P428Faithful ell M R (fun k Lu _ _ Lam => junkIngr ell (by omega) k Lu Lam) := by
  refine ⟨⟨hell, hM, hR⟩, 1, one_pos, 1, one_pos, ?_⟩
  intro k Lu f _ α₀ _ _ _ S _ Lam _ U _ Bt _ _
  show 1 * bondEnergy Bt ≤ (junkIngr ell (by omega) k Lu Lam).form _
  rw [form_junk]
  have := AdalyFormal.Balaban.IslandBridge.norm_sq_bondFnL2 (L := Lu) Bt
  simp only [junkIngr, LinearMap.id_coe, id_eq]
  rw [this]
  linarith

#print axioms junk_satisfies_P428Faithful

open AdalyFormal.StatementLane2 in
/-- **MUST-FIRE (D1).**  The round-1 junk family (Q coisometry, G1 = id, a = 0, H1 = D2 = J = Q1 = 0,
C = id) is NOT in the ingredient class `IngrB`: its `H1` is `0` (and its `a` is `0`). -/
theorem junk_not_IngrB (hell : 0 < 2) :
    IsEmpty (IngrB 2 hell (fun k Lu _ _ Lam => junkIngr 2 (by omega) k Lu Lam)) :=
  IngrB.not_of_H1_zero (hell := hell) _ 0 L10 (fun μ => by simp [L10])
    ⟨fun _ => ∅⟩ (fun _ => 1) Set.univ rfl

open AdalyFormal.StatementLane2 in
theorem junk_not_IngrB_a (hell : 0 < 2) :
    IsEmpty (IngrB 2 hell (fun k Lu _ _ Lam => junkIngr 2 (by omega) k Lu Lam)) :=
  IngrB.not_of_a_nonpos (hell := hell) _ 0 L10 (fun μ => by simp [L10])
    ⟨fun _ => ∅⟩ (fun _ => 1) Set.univ (le_refl _)

#print axioms junk_not_IngrB
#print axioms junk_not_IngrB_a

end AdalyFormal.StatementLane2.JunkCopy
