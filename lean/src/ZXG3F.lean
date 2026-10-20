import ZXG3D3

/-!
# G3F -- `WellDef` at `k = 0`, flat `U`, for ANY single-level tower `S` (`S.Om 1 = ∅`, e.g. every
`Admissible` tower of height 0, in particular the PROPER tower `T40` with `Ω₀ ≠` torus).
On such towers `τ` is not surjective, so the ingredient lane's `toIngr.hunit` is FALSE (G3E
`toIngr_hunit_false`), but the (3.155)-faithful `WellDef` (multi-level `Nmat` on `L²(𝔅)`) holds.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- `k = 0`, flat background, ANY tower `S` -/
def P1 (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (S : Tower (scaleUp ell 0 Lu)) : IngrBParams :=
  ⟨ell, 0, Lu, hell, S, flatCfg, a, Lam⟩

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu)) (S : Tower (scaleUp ell 0 Lu)) (hS1 : S.Om 1 = ∅)

local notation "PP" => P1 ell Lu hell a Lam S

include hS1

theorem P1_Lam0 : (PP).G.Lam 0 = S.Om 0 := by
  ext x
  show x ∈ (geomOf ell 0 S).Lam 0 ↔ _
  simp [geomOf, hS1]
  exact Iff.rfl

theorem P1_bondsLam0 (b : Bond (scaleUp ell 0 Lu)) :
    b ∈ bondsLam (PP).G 0 ↔ b ∈ bondsOm0 (PP).G := by
  have h := P1_Lam0 ell Lu hell a Lam S hS1
  have hOm : (PP).G.Om0 = S.Om 0 := rfl
  have hshift : AdalyFormal.Balaban.CoarseCurl.coarseShift b.1 ((PP).G.ell ^ 0) b.2 =
      periodicLatticeShift b.1 b.2 := rfl
  have hk : (PP).G.k = 0 := rfl
  have hno : ¬ (OmGe (PP).G (0 + 1) b.1 ∨ OmGe (PP).G (0 + 1)
      (AdalyFormal.Balaban.CoarseCurl.coarseShift b.1 ((PP).G.ell ^ 0) b.2)) :=
    fun hh => hh.elim (not_OmGe_of_lt (by omega) _) (not_OmGe_of_lt (by omega) _)
  show ((b.1 ∈ (PP).G.Lam 0 ∨ AdalyFormal.Balaban.CoarseCurl.coarseShift b.1 ((PP).G.ell ^ 0) b.2 ∈ (PP).G.Lam 0) ∧
      ¬ (OmGe (PP).G (0 + 1) b.1 ∨ OmGe (PP).G (0 + 1)
      (AdalyFormal.Balaban.CoarseCurl.coarseShift b.1 ((PP).G.ell ^ 0) b.2))) ↔
    (b.1 ∈ (PP).G.Om0 ∨ periodicLatticeShift b.1 b.2 ∈ (PP).G.Om0)
  rw [and_iff_left hno, hshift, h, hOm]

theorem P1_bidx_mem (p : BIdx (PP).G) : p.2.1 ∈ bondsOm0 (PP).G := by
  obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := p
  have hj1 : j < 1 := hj
  have hj0 : j = 0 := by omega
  subst hj0
  exact (P1_bondsLam0 ell Lu hell a Lam S hS1 b).mp hb

/-- `BIdx ≃ {b // b ∈ bondsOm0}` at `k = 0` -/
noncomputable def idx1 : {b : Bond (scaleUp ell 0 Lu) // b ∈ bondsOm0 (PP).G} ≃ BIdx (PP).G where
  toFun b := ⟨⟨0, by simp [P1]⟩, ⟨b.1, (P1_bondsLam0 ell Lu hell a Lam S hS1 b.1).mpr b.2⟩⟩
  invFun p := ⟨p.2.1, P1_bidx_mem ell Lu hell a Lam S hS1 p⟩
  left_inv b := rfl
  right_inv p := by
    obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := p
    have hj1 : j < 1 := hj
    have hj0 : j = 0 := by omega
    subst hj0
    rfl

theorem P1_QlinB (A : BondFnL2 (scaleUp ell 0 Lu)) :
    QlinB (PP).G (PP).U 0 A = A :=
  QlinB_zero _ _ A

theorem P1_Qfull_apply (A : BondFnL2 (scaleUp ell 0 Lu)) (p : BIdx (PP).G) :
    ((PP).sector.Qfull A) p = (WithLp.ofLp A) p.2.1 := by
  have hp : (p.1 : ℕ) = 0 := by
    have : (p.1 : ℕ) < 1 := p.1.isLt
    omega
  have key : ∀ (j : ℕ) (b : Bond (scaleUp ell 0 Lu)), j = 0 →
      (((PP).G.ell : ℝ) ^ j)⁻¹ • (WithLp.ofLp (QlinB (PP).G (PP).U j A)) b = (WithLp.ofLp A) b := by
    intro j b hj
    subst hj
    rw [P1_QlinB ell Lu hell a Lam S hS1, pow_zero, inv_one, one_smul]
  exact key (p.1 : ℕ) p.2.1 hp

/-- `Σ_p ‖y p.2.1‖² = ‖y‖²` for `y` supported in `Ω₀` bonds -/
theorem P1_sum_index (y : BondFnL2 (scaleUp ell 0 Lu)) (hy : ∀ b, b ∉ bondsOm0 (PP).G → (WithLp.ofLp y) b = 0) :
    ∑ p : BIdx (PP).G, ‖(WithLp.ofLp y) p.2.1‖ ^ 2 = ‖y‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have e1 : ∑ p : BIdx (PP).G, ‖(WithLp.ofLp y) p.2.1‖ ^ 2
      = ∑ b : {b : Bond (scaleUp ell 0 Lu) // b ∈ bondsOm0 (PP).G}, ‖(WithLp.ofLp y) b.1‖ ^ 2 :=
    (Fintype.sum_equiv (idx1 ell Lu hell a Lam S hS1) (fun b => ‖(WithLp.ofLp y) b.1‖ ^ 2)
      (fun p => ‖(WithLp.ofLp y) p.2.1‖ ^ 2) (fun b => rfl)).symm
  have e2 : ∑ b : {b : Bond (scaleUp ell 0 Lu) // b ∈ bondsOm0 (PP).G}, ‖(WithLp.ofLp y) b.1‖ ^ 2
      = ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsOm0 (PP).G), ‖(WithLp.ofLp y) b‖ ^ 2 :=
    (Finset.sum_subtype (Finset.univ.filter (fun b => b ∈ bondsOm0 (PP).G))
      (p := fun b => b ∈ bondsOm0 (PP).G) (by intro b; simp) (fun b => ‖(WithLp.ofLp y) b‖ ^ 2)).symm
  have e3 : ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsOm0 (PP).G), ‖(WithLp.ofLp y) b‖ ^ 2
      = ∑ b, ‖(WithLp.ofLp y) b‖ ^ 2 := by
    refine Finset.sum_filter_of_ne (fun b _ hne => ?_)
    by_contra hb
    exact hne (by rw [hy b hb]; simp)
  rw [e1, e2, e3]

theorem P1_mass_inner (x : ↥(bondSupp (PP).G)) :
    ⟪x, (PP).data.Mass x⟫ = a * ‖x‖ ^ 2 := by
  have h1 : ⟪x, (PP).data.Mass x⟫ = ⟪iE (PP).G x, MassFull (PP).G (PP).a (PP).sector (iE (PP).G x)⟫ := by
    show ⟪x, (pE (PP).G) ((MassFull (PP).G (PP).a (PP).sector) ((iE (PP).G) x))⟫ = _
    rw [pE_inner_right]
  rw [h1, inner_MassFull]
  have h2 : ∀ p : BIdx (PP).G,
      (PP).a * ((PP).G.ell : ℝ) ^ (p.1 : ℕ) * ‖(PP).sector.Qfull (iE (PP).G x) p‖ ^ 2
        = a * ‖(WithLp.ofLp (iE (PP).G x)) p.2.1‖ ^ 2 := by
    intro p
    have hp : (p.1 : ℕ) = 0 := by
      have : (p.1 : ℕ) < 1 := p.1.isLt
      omega
    have key : ∀ (j : ℕ), j = 0 →
        (PP).a * ((PP).G.ell : ℝ) ^ j * ‖(PP).sector.Qfull (iE (PP).G x) p‖ ^ 2
          = a * ‖(PP).sector.Qfull (iE (PP).G x) p‖ ^ 2 := by
      intro j hj; subst hj; rw [pow_zero, mul_one]; rfl
    rw [key _ hp, P1_Qfull_apply ell Lu hell a Lam S hS1]
  rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.mul_sum,
    P1_sum_index ell Lu hell a Lam S hS1 (iE (PP).G x) (fun b hb => x.2 b hb)]
  rfl

theorem P1_Ginv_coercive (x : ↥(bondSupp (PP).G)) :
    a * ‖x‖ ^ 2 ≤ ⟪x, (PP).data.Ginv x⟫ := by
  rw [BaseDataS.inner_Ginv, P1_mass_inner ell Lu hell a Lam S hS1]
  have hD : 0 ≤ ⟪x, (PP).data.Dpi x⟫ := by
    show 0 ≤ ⟪x, (pE (PP).G) ((DpiFull (PP).G (PP).U (PP).a) ((iE (PP).G) x))⟫
    rw [pE_inner_right]
    exact DpiFull_flat_nonneg (PP).G (PP).a _
  have hT : 0 ≤ ‖(PP).data.T x‖ ^ 2 := sq_nonneg _
  linarith

theorem P1_Delta2_zero : (PP).data.Delta2 (PP).data_laws = 0 := by
  obtain ⟨hs, hf⟩ := (PP).data.Delta2_spec (PP).data_laws
  refine symm_unique hs (fun x y => by simp) (fun A => ?_)
  rw [hf A]
  have hJ : (PP).data.J = 0 := by
    show (pE (PP).G) (PP).Jf = 0
    rw [Jf_flat (PP) rfl]; exact map_zero _
  rw [hJ]; simp

theorem P1_Qs_injective : Function.Injective (PP).data.Qs := by
  classical
  have hsurj : ∀ f : FSp (PP).G, ∃ A : ↥(bondSupp (PP).G), (PP).data.Q A = f := by
    intro f
    refine ⟨⟨WithLp.toLp 2 (fun b => if hb : b ∈ bondsOm0 (PP).G
        then (WithLp.ofLp f) (idx1 ell Lu hell a Lam S hS1 ⟨b, hb⟩) else 0), ?_⟩, ?_⟩
    · intro b hb
      simp [hb]
    · refine PiLp.ext (fun p => ?_)
      show (PP).sector.Qfull ((iE (PP).G) _) p = _
      rw [P1_Qfull_apply ell Lu hell a Lam S hS1]
      have hmem : p.2.1 ∈ bondsOm0 (PP).G := P1_bidx_mem ell Lu hell a Lam S hS1 p
      show (if hb : p.2.1 ∈ bondsOm0 (PP).G then _ else _) = _
      rw [dif_pos hmem]
      have hp : idx1 ell Lu hell a Lam S hS1 ⟨p.2.1, hmem⟩ = p := by
        obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := p
        have hj1 : j < 1 := hj
        have hj0 : j = 0 := by omega
        subst hj0
        rfl
      rw [hp]
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨A, hA⟩ := hsurj y
  have h1 : ⟪(PP).data.Q A, y⟫ = ⟪A, (PP).data.Qs y⟫ := (PP).data.Q_adj A y
  rw [hy, inner_zero_right, hA] at h1
  exact inner_self_eq_zero.mp h1

/-- **`WellDef` for ANY single-level tower, flat `U`, `0 < a`, `ell ∣ Lu μ + 1`.** -/
theorem P1_wellDef (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) : GenP.WellDef (PP) := by
  have hco : ∀ x, a * ‖x‖ ^ 2 ≤ ⟪x, (PP).data.Ginv x⟫ :=
    fun x => P1_Ginv_coercive ell Lu hell a Lam S hS1 x
  have hε : ‖(PP).data.Delta2 (PP).data_laws‖ ≤ 0 := by
    rw [P1_Delta2_zero ell Lu hell a Lam S hS1]; exact le_of_eq ContinuousLinearMap.opNorm_zero
  have hG := (PP).G1inv_spec
  have hco1 := (PP).data.G1inv_coercive (PP).data_laws hG hco hε
  refine ⟨IngrBParams.hb_flat (PP) rfl hdvd, ?_, ?_⟩
  · exact isUnit_of_coercive _ ha (fun x => by simpa using hco1 x)
  · exact (PP).data.QG1Qs_isUnit_of_small (PP).data_laws hG (c := a) (ε := 0) ha hco hε
      (P1_Qs_injective ell Lu hell a Lam S hS1)

end

#print axioms P1_wellDef

end AdalyFormal.StatementLaneG
