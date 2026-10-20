import ZR2A

/-!
# R2B1 -- D2 controls: (i) MUST-FIRE: the r1-prosecution tower `Sthin` (R=1) is excluded by
`CoversOm0`; (ii) MUST-NOT-FIRE: the constant tower covers, for every k.
`Sthin`, `Om0`, `LamThin` and the proofs `Sthin_admissible`, `LamThin_ok` are copied from
compute/statement_lane_20261009_prosecution_claude/src/Thin.lean (read-only source, credited).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

/- (r5: the r1-prosecution tower `Sthin` (`k = 0`, `Ω₀ = {x₀ ≤ 2}` nonempty with `Ω₁ = ∅`) is NOT admissible any more (r5 (2)); its D2 must-fire role
   is taken by `ZT5Controls` at `k = 1`.) -/

/-! ## MUST-NOT-FIRE: the constant tower covers (k arbitrary), cube = whole fine torus -/

theorem Sk_coversc (k c : ℕ) (hc : 0 < c) {L : PeriodicLatticeExtent}
    (hdiv : ∀ μ : Fin 3, 2 ^ k ∣ L μ + 1) (hle : ∀ μ : Fin 3, L μ + 1 ≤ c * 2 ^ k) :
    CoversOm0c 2 1 c k (Sk L k) := by
  intro x _
  have hsz : 0 < c * bigSide 1 2 k := by simp [bigSide]; omega
  have hB : ∀ i, i < k → towerBj (Sk L k) i = ∅ := by
    intro i hi
    have h1 : i ≤ k := by omega
    have h2 : i + 1 ≤ k := by omega
    ext y
    simp [towerBj, Sk, h1, h2]
  have hBk : towerBj (Sk L k) k = Set.univ := by
    ext y
    simp [towerBj, Sk]
  have hnon : (siteBox (L := L) (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide 1 2 k)
      ∩ towerBj (Sk L k) k).Nonempty := by
    refine ⟨fun μ => ⟨0, Nat.succ_pos _⟩, ?_, by rw [hBk]; exact Set.mem_univ _⟩
    intro μ
    simpa using hsz
  refine ⟨siteBox (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide 1 2 k), k,
    ⟨⟨le_refl k, ⟨_, ?_, rfl⟩, ?_, hnon⟩, ?_⟩, ?_⟩
  · intro μ; simp
  · intro y _; left; rw [hBk]; exact Set.mem_univ _
  · intro i hi
    by_contra hne
    have hlt : i < k := lt_of_le_of_ne hi.1 hne
    obtain ⟨y, _, hy⟩ := hi.2.2.2
    rw [hB i hlt] at hy
    exact hy
  · intro μ
    have h1 := (x μ).isLt
    have h2 := hle μ
    have : ((x μ).val + (L μ + 1) - 0) % (L μ + 1) = (x μ).val := by
      rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
    simp only [bigSide, this, one_mul]
    exact lt_of_lt_of_le h1 h2

theorem Sk_covers (k F : ℕ) (hF : 10 ≤ F) {L : PeriodicLatticeExtent}
    (hdiv : ∀ μ : Fin 3, 2 ^ k ∣ L μ + 1) (hle : ∀ μ : Fin 3, L μ + 1 ≤ 10 * 2 ^ k) :
    CoversOm0 2 1 F k (Sk L k) :=
  (Sk_coversc k 10 (by norm_num) hdiv hle).toRange (le_refl _) hF

theorem Sk_covers_scaleUp (k F : ℕ) (hF : 10 ≤ F) :
    CoversOm0 2 1 F k (Sk (scaleUp 2 k L10) k) := by
  have hf : ∀ μ, scaleUp 2 k L10 μ + 1 = 10 * 2 ^ k := by
    intro μ
    have : 0 < 10 * 2 ^ k := by positivity
    simp only [scaleUp, L10]
    have : (9 + 1) * 2 ^ k = 10 * 2 ^ k := by norm_num
    omega
  exact Sk_covers k F hF (fun μ => by rw [hf μ]; exact Dvd.intro_left _ rfl)
    (fun μ => by rw [hf μ])

theorem Sk_coversc_scaleUp (k c : ℕ) (hc : 10 ≤ c) :
    CoversOm0c 2 1 c k (Sk (scaleUp 2 k L10) k) := by
  have hf : ∀ μ, scaleUp 2 k L10 μ + 1 = 10 * 2 ^ k := by
    intro μ
    have : 0 < 10 * 2 ^ k := by positivity
    simp only [scaleUp, L10]
    have : (9 + 1) * 2 ^ k = 10 * 2 ^ k := by norm_num
    omega
  exact Sk_coversc k c (by omega) (fun μ => by rw [hf μ]; exact Dvd.intro_left _ rfl)
    (fun μ => by rw [hf μ]; exact Nat.mul_le_mul_right _ hc)

#print axioms Sk_coversc
#print axioms Sk_coversc_scaleUp
#print axioms Sk_covers
#print axioms Sk_covers_scaleUp

end AdalyFormal.StatementLane2
