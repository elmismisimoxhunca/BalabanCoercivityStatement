import ZXR2Unit2
import ZIngredientQ1
import AdalyFormal.Balaban.FullReparamC

/-!
# R2Unit3 -- at the FLAT background `H₀ = ell⁻³ · id`: `C` and `h` exist (so `hb` of `toIngr` is
satisfiable), by the tree's decoupling/hit-count lemmas (`droppedBondLast_not_reads`, `hit_unique`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice mem_blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast ReadsBond droppedBondLast_not_reads
  coarse_coord_add_ell_le)
open AdalyFormal.Balaban.FullReparamC (hit_unique pathSite_mem_block pathSite_add)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.StatementLane (LamPrime)
open AdalyFormal.IngredientFamily (q1SU2)

variable {L : PeriodicLatticeExtent}

theorem H0_q1SU2_apply {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (w : Dset L ell Lam → SuTwo) (c : Dset L ell Lam) :
    H0 Lam (q1SU2 ell) w c = ((1 : ℝ) / (ell : ℝ) ^ 3) • w c := by
  classical
  have hfit : ((c.1.1.1) c.1.2).val + ell ≤ L c.1.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.1.2 _ (mem_CoarseLattice.mp c.1.1.2 c.1.2) (c.1.1.1 c.1.2).isLt
  -- the inner `c'`-sum collapses to `c' = c`
  have hcollapse : ∀ x ∈ blockOf c.1.1.1 ell, ∀ i ∈ Finset.range ell,
      iotaD ell Lam w (pathSite x c.1.2 i, c.1.2)
        = if x = pathSite c.1.1.1 c.1.2 (ell - 1 - i) then w c else 0 := by
    intro x hx i hi
    have hi' : i < ell := Finset.mem_range.mp hi
    show (∑ c' : Dset L ell Lam, if (pathSite x c.1.2 i, c.1.2) = droppedBondLast ell c'.1 then w c' else 0) = _
    rw [Finset.sum_eq_single c]
    · -- the `c' = c` term
      have hiff : ((pathSite x c.1.2 i, c.1.2) = droppedBondLast ell c.1)
          ↔ x = pathSite c.1.1.1 c.1.2 (ell - 1 - i) := by
        constructor
        · intro h
          have h1 : pathSite x c.1.2 i = pathSite c.1.1.1 c.1.2 (ell - 1) := congrArg Prod.fst h
          exact hit_unique hell c.1.1.1 c.1.2 hfit x hx i hi' h1
        · intro h
          refine Prod.ext ?_ rfl
          show pathSite x c.1.2 i = pathSite c.1.1.1 c.1.2 (ell - 1)
          rw [h, pathSite_add]
          congr 1; omega
      simp only [hiff]
    · intro c' _ hne
      have hne' : c.1 ≠ c'.1 := fun h => hne (Subtype.ext h.symm)
      have : ¬ ((pathSite x c.1.2 i, c.1.2) = droppedBondLast ell c'.1) := fun h =>
        droppedBondLast_not_reads hell hdvd c.1 c'.1 hne' ⟨x, hx, i, hi, h⟩
      simp [this]
    · intro h; exact absurd (Finset.mem_univ c) h
  have hsum : ∑ x ∈ blockOf c.1.1.1 ell, ∑ i ∈ Finset.range ell,
      iotaD ell Lam w (pathSite x c.1.2 i, c.1.2) = (ell : ℝ) • w c := by
    rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (hcollapse x hx))]
    rw [Finset.sum_comm]
    have : ∀ i ∈ Finset.range ell,
        ∑ x ∈ blockOf c.1.1.1 ell, (if x = pathSite c.1.1.1 c.1.2 (ell - 1 - i) then w c else 0) = w c := by
      intro i hi
      have hi' : i < ell := Finset.mem_range.mp hi
      rw [Finset.sum_ite_eq' (blockOf c.1.1.1 ell) (pathSite c.1.1.1 c.1.2 (ell - 1 - i)) (fun _ => w c)]
      rw [if_pos (pathSite_mem_block hell c.1.1.1 c.1.2 _ (by omega) hfit)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul ℝ]
  show (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf c.1.1.1 ell, ∑ i ∈ Finset.range ell,
      iotaD ell Lam w (pathSite x c.1.2 i, c.1.2) = _
  rw [hsum, smul_smul]
  congr 1
  field_simp

/-- `H₀` at the flat background is the nonzero scalar `ell⁻³`: bijective. -/
theorem H0_q1SU2_bijective {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) : Function.Bijective (H0 Lam (q1SU2 ell)) := by
  have hne : ((1 : ℝ) / (ell : ℝ) ^ 3) ≠ 0 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have hH : H0 Lam (q1SU2 ell) = ((1 : ℝ) / (ell : ℝ) ^ 3) • LinearMap.id := by
    refine LinearMap.ext (fun w => ?_)
    funext c
    exact H0_q1SU2_apply hell hdvd Lam w c
  rw [hH]
  refine ⟨fun a b h => ?_, fun y => ⟨((1 : ℝ) / (ell : ℝ) ^ 3)⁻¹ • y, ?_⟩⟩
  · have := congrArg (fun z => (((1 : ℝ) / (ell : ℝ) ^ 3)⁻¹) • z) h
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, inv_mul_cancel₀ hne,
      one_smul] at this
    exact this
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ hne, one_smul]

#print axioms H0_q1SU2_bijective

end AdalyFormal.IngredientFamilyR2
