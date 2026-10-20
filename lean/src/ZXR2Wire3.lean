import ZXR2Wire2

/-!
# R2Wire3 -- the full-support case: `τ` is a bijection
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)

theorem embY_injective (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) :
    Function.Injective (embY ell k Lu hell) := by
  intro y y' h
  funext μ
  have := congrFun h μ
  have h1 : ell ^ k * (y μ).val = ell ^ k * (y' μ).val := congrArg Fin.val this
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left (pow_pos hell k) h1)

theorem unitBondEmb_injective (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) :
    Function.Injective (unitBondEmb ell k Lu hell) := by
  intro e e' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (embY_injective ell k Lu hell h1) h2

namespace IngrBParams
variable (P : IngrBParams)

/-- FULL SUPPORT: no level `j < k` constraint bonds, and the level-`k` bonds of `𝔅` are exactly the
embedded unit bonds (e.g. `Ω_j = ` whole torus for `j ≤ k`, `Ω_{k+1} = ∅`). -/
def FullSupp : Prop :=
  (∀ j : ℕ, j < P.k → bondsLam P.G j = ∅) ∧
  (∀ b : Bond (scaleUp P.ell P.k P.Lu), b ∈ bondsLam P.G P.k ↔
    ∃ e : Bond P.Lu, b = unitBondEmb P.ell P.k P.Lu P.hell e)

theorem mem_of_fullSupp (h : P.FullSupp) (e : Bond P.Lu) :
    unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k := (h.2 _).mpr ⟨e, rfl⟩

/-- the index equivalence `unit bonds ≃ 𝔅` in the full-support case. -/
noncomputable def eqv (h : P.FullSupp) : Bond P.Lu ≃ BIdx P.G :=
  Equiv.ofBijective
    (fun e => ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, P.mem_of_fullSupp h e⟩⟩)
    ⟨fun e e' he => by
      have := congrArg (fun p : BIdx P.G => p.2.1) he
      exact unitBondEmb_injective P.ell P.k P.Lu P.hell this,
     fun p => by
      obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := p
      have hjk : j ≤ P.k := Nat.lt_succ_iff.mp hj
      by_cases hlt : j < P.k
      · exact absurd hb (by rw [h.1 j hlt]; exact Set.notMem_empty b)
      · have hjeq : j = P.k := le_antisymm hjk (not_lt.mp hlt)
        subst hjeq
        obtain ⟨e, rfl⟩ := (h.2 b).mp hb
        exact ⟨e, rfl⟩⟩

theorem tau_apply (h : P.FullSupp) (f : FSp P.G) (e : Bond P.Lu) :
    (WithLp.ofLp (P.tau f)) e = (WithLp.ofLp f) (P.eqv h e) := by
  classical
  show (if hb : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam (geomOf P.ell P.k P.S) P.k
        then WithLp.ofLp f ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, hb⟩⟩ else 0) = _
  rw [dif_pos (P.mem_of_fullSupp h e)]
  rfl

theorem tau_bijective (h : P.FullSupp) : Function.Bijective P.tau := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    refine PiLp.ext (fun p => ?_)
    obtain ⟨e, rfl⟩ := (P.eqv h).surjective p
    have := congrArg (fun g : BondFnL2 P.Lu => WithLp.ofLp g e) hf
    simp only [tau_apply P h] at this
    simpa using this
  · intro B
    refine ⟨WithLp.toLp 2 (fun p => (WithLp.ofLp B) ((P.eqv h).symm p)), ?_⟩
    refine PiLp.ext (fun e => ?_)
    rw [tau_apply P h]
    simp


#print axioms tau_bijective

end IngrBParams

/-! ## non-vacuity of `FullSupp`: the full tower `Ω_j = ` whole torus for `j ≤ k`, `∅` beyond -/

/-- `Ω_j = univ` for `j ≤ k`, `Ω_j = ∅` for `j > k` (so `Ω_{k+1} = ∅` as printed). -/
def fullTower (ell k : ℕ) (Lu : PeriodicLatticeExtent) : Tower (scaleUp ell k Lu) where
  Om := fun j => if j ≤ k then Set.univ else ∅

theorem fullTower_lam_lt (ell k : ℕ) (Lu : PeriodicLatticeExtent) (j : ℕ) (hj : j < k) :
    (geomOf ell k (fullTower ell k Lu)).Lam j = ∅ := by
  ext x
  have h1 : j + 1 ≤ k := hj
  simp [geomOf, fullTower, hj.le, hj]

theorem fullTower_lam_k (ell k : ℕ) (Lu : PeriodicLatticeExtent) (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    x ∈ (geomOf ell k (fullTower ell k Lu)).Lam k ↔ ∀ μ : Fin 3, ell ^ k ∣ (x μ).val := by
  simp [geomOf, fullTower]


open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

theorem scaleUp_succ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  unfold scaleUp
  have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- level-`k` coarse sites of the fine torus are exactly the embedded unit sites. -/
theorem coarse_k_iff_emb (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    (∀ μ : Fin 3, ell ^ k ∣ (x μ).val) ↔ ∃ y : PeriodicLatticeSite Lu, x = embY ell k Lu hell y := by
  constructor
  · intro h
    refine ⟨fun μ => ⟨(x μ).val / ell ^ k, ?_⟩, ?_⟩
    · have h1 : (x μ).val < (Lu μ + 1) * ell ^ k :=
        lt_of_lt_of_eq (x μ).isLt (scaleUp_succ ell k Lu hell μ)
      exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using h1)
    · funext μ
      apply Fin.ext
      show (x μ).val = ell ^ k * ((x μ).val / ell ^ k)
      exact (Nat.mul_div_cancel' (h μ)).symm
  · rintro ⟨y, rfl⟩ μ
    exact dvd_mul_right _ _

theorem fullTower_bondsLam_k (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (b : Bond (scaleUp ell k Lu)) :
    b ∈ bondsLam (geomOf ell k (fullTower ell k Lu)) k ↔
      ∃ e : Bond Lu, b = unitBondEmb ell k Lu hell e := by
  constructor
  · intro hb0
    have hb := hb0.1
    have hc : ∀ ν : Fin 3, ell ^ k ∣ (b.1 ν).val := by
      rcases hb with h1 | h1
      · exact (fullTower_lam_k ell k Lu b.1).mp h1
      · have h2 := (fullTower_lam_k ell k Lu _).mp h1
        intro ν
        have h3 := h2 ν
        by_cases hν : ν = b.2
        · subst hν
          have hN : ell ^ k ∣ scaleUp ell k Lu b.2 + 1 := by
            rw [scaleUp_succ ell k Lu hell]; exact dvd_mul_left _ _
          show ell ^ k ∣ ((b.1 b.2).val)
          have h4 : ell ^ k ∣ ((coarseShift b.1 (ell ^ k) b.2) b.2).val := h3
          rw [coarseShift_val_eq, Nat.dvd_mod_iff hN] at h4
          exact (Nat.dvd_add_left (dvd_refl _)).mp h4
        · have h4 : ell ^ k ∣ ((coarseShift b.1 (ell ^ k) b.2) ν).val := h3
          rw [coarseShift_apply_ne _ _ _ _ hν] at h4
          exact h4
    obtain ⟨y, hy⟩ := (coarse_k_iff_emb ell k Lu hell b.1).mp hc
    exact ⟨(y, b.2), Prod.ext hy rfl⟩
  · rintro ⟨e, rfl⟩
    refine ⟨Or.inl ((fullTower_lam_k ell k Lu _).mpr ((coarse_k_iff_emb ell k Lu hell _).mpr ⟨e.1, rfl⟩)),
      fun hh => hh.elim (not_OmGe_of_lt (by show k < k + 1; omega) _) (not_OmGe_of_lt (by show k < k + 1; omega) _)⟩

/-- The full tower satisfies `FullSupp` for every `U`, `a`, `Λ`. -/
theorem fullTower_fullSupp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    IngrBParams.FullSupp ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩ := by
  refine ⟨fun j hj => ?_, fun b => fullTower_bondsLam_k ell k Lu hell b⟩
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  have : (geomOf ell k (fullTower ell k Lu)).Lam j = ∅ := fullTower_lam_lt ell k Lu j hj
  intro hh
  rcases hh.1 with h1 | h1 <;> exact (Set.eq_empty_iff_forall_notMem.mp this) _ h1

#print axioms fullTower_fullSupp

end AdalyFormal.IngredientFamilyR2
