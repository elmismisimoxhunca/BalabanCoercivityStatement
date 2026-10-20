import ZR2B2

/-!
# R2B3 -- MAIN CONTROL (D2): the regularity class excludes a large-holonomy `U`.
For ANY class cube of ANY tower (with `F M α₀ ≤ 1/2`), the configuration `badU z` (all links 1
except one link `−1`, so one plaquette has holonomy `−1`) is NOT in `PerCubeRegular2`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

theorem off_self (N a : ℕ) : (a + N - a) % N = 0 := by
  rw [Nat.add_sub_cancel_left]; exact Nat.mod_self N

theorem off_succ (N a : ℕ) (ha : a < N) (hN : 2 ≤ N) : (((a + 1) % N) + N - a) % N = 1 := by
  rcases Nat.lt_or_ge (a + 1) N with h | h
  · rw [Nat.mod_eq_of_lt h]
    have : a + 1 + N - a = N + 1 := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · have h' : a + 1 = N := by omega
    rw [h', Nat.mod_self]
    have : 0 + N - a = 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]

theorem shift_apply {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) (a μ : Fin 3) :
    (periodicLatticeShift z a) μ = if μ = a then z μ + 1 else z μ := by
  unfold periodicLatticeShift
  by_cases h : μ = a
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [h]

theorem fin_succ_val {L : PeriodicLatticeExtent} (μ : Fin 3) (hN : 1 ≤ L μ)
    (c : Fin (L μ + 1)) : (c + 1).val = ((c.val + 1) % (L μ + 1)) := by
  rw [Fin.val_add]
  have : (1 : Fin (L μ + 1)).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [this]

theorem off_lt_two {L : PeriodicLatticeExtent} (z w : PeriodicLatticeSite L) (μ : Fin 3)
    (hN : 1 ≤ L μ) (hw : w μ = z μ ∨ w μ = z μ + 1) :
    ((w μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < 2 := by
  rcases hw with h | h
  · rw [h, off_self]; omega
  · rw [h, fin_succ_val μ hN, off_succ _ _ (z μ).isLt (by omega)]; omega

theorem mem_box_two {L : PeriodicLatticeExtent} (z w : PeriodicLatticeSite L) (s : ℕ) (hs : 2 ≤ s)
    (hN : ∀ μ, 1 ≤ L μ) (hw : ∀ μ, w μ = z μ ∨ w μ = z μ + 1) : w ∈ siteBox z s := by
  intro μ
  exact lt_of_lt_of_le (off_lt_two z w μ (hN μ) (hw μ)) hs

theorem hw_self {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) :
    ∀ μ, z μ = z μ ∨ z μ = z μ + 1 := fun _ => Or.inl rfl

theorem hw_shift {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) (a : Fin 3) :
    ∀ μ, (periodicLatticeShift z a) μ = z μ ∨ (periodicLatticeShift z a) μ = z μ + 1 := by
  intro μ; rw [shift_apply]; by_cases h : μ = a <;> simp [h]

theorem hw_shift2 {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) :
    ∀ μ, (periodicLatticeShift (periodicLatticeShift z 0) 1) μ = z μ ∨
      (periodicLatticeShift (periodicLatticeShift z 0) 1) μ = z μ + 1 := by
  intro μ
  rw [shift_apply, shift_apply]
  fin_cases μ <;> simp

theorem shift_ne_self {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) (a : Fin 3)
    (hN : 1 ≤ L a) : periodicLatticeShift z a ≠ z := by
  intro h
  have := congrFun h a
  rw [shift_apply] at this
  simp only [if_true] at this
  have h2 := congrArg Fin.val this
  rw [fin_succ_val a hN] at h2
  have h3 := (z a).isLt
  rcases Nat.lt_or_ge ((z a).val + 1) (L a + 1) with h4 | h4
  · rw [Nat.mod_eq_of_lt h4] at h2; omega
  · have : (z a).val + 1 = L a + 1 := by omega
    rw [this, Nat.mod_self] at h2
    omega

/-- (1/2 bound) for a bond in the cube -/
theorem bond_dist_lt {ell M f j : ℕ} {α₀ η : ℝ} (hell : 1 ≤ ell) (hη : 0 < η) (hα : 0 < α₀)
    (hsmall : (f : ℝ) * M * α₀ ≤ 1 / 2) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) : η * x < 1 / 2 := by
  have hell' : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : (1 : ℝ) ≤ (ell : ℝ) ^ j := one_le_pow₀ hell'
  have hpos : 0 < (ell : ℝ) ^ j * η := by positivity
  have hB : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  have h1 : η * x < η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) :=
    mul_lt_mul_of_pos_left hx hη
  have h2 : η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) = (f : ℝ) * M * α₀ / (ell : ℝ) ^ j := by
    field_simp
  have h3 : (f : ℝ) * M * α₀ / (ell : ℝ) ^ j ≤ (f : ℝ) * M * α₀ := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **MAIN.** A class cube (index `j`, size `f ≥ 10`) forces regularity to fail for `badU z`. -/
theorem badU_not_perCubeRegular2 {L : PeriodicLatticeExtent} (hN : ∀ μ, 1 ≤ L μ)
    {ell M f k : ℕ} (hell : 1 ≤ ell) (hM : 1 ≤ M) (hf : 10 ≤ f) (S : Tower L)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 < α₀) (hsmall : (f : ℝ) * M * α₀ ≤ 1 / 2)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hc : IsClassCube ell M f k S sites j) :
    ∃ U : LinkCfg L, ¬ PerCubeRegular2 ell M f k S α₀ η U := by
  obtain ⟨⟨hj, ⟨z, hgc, hsites⟩, hsub, hne⟩, huniq⟩ := hc
  refine ⟨badU z, ?_⟩
  intro hreg
  obtain ⟨g, A, hA, -, -⟩ := hreg sites j ⟨⟨hj, ⟨z, hgc, hsites⟩, hsub, hne⟩, huniq⟩
  have hs2 : 2 ≤ f * bigSide M ell j := by
    unfold bigSide
    have : 1 ≤ M * ell ^ j := Nat.mul_pos hM (pow_pos hell j)
    nlinarith
  have m0 : z ∈ sites := hsites ▸ mem_box_two z z _ hs2 hN (hw_self z)
  have m1 : periodicLatticeShift z 0 ∈ sites := hsites ▸ mem_box_two z _ _ hs2 hN (hw_shift z 0)
  have m2 : periodicLatticeShift z 1 ∈ sites := hsites ▸ mem_box_two z _ _ hs2 hN (hw_shift z 1)
  have m3 : periodicLatticeShift (periodicLatticeShift z 0) 1 ∈ sites :=
    hsites ▸ mem_box_two z _ _ hs2 hN (hw_shift2 z)
  have m4 : periodicLatticeShift (periodicLatticeShift z 1) 0 ∈ sites := by
    rw [← shift_comm01]; exact m3
  -- each of the four cube bonds is within 1/2 of 1
  have key : ∀ e : Bond L, CubeBond sites e →
      dist1 (periodicGaugeTransform g (badU z) e) < 1 / 2 := by
    intro e he
    obtain ⟨hHT, hexp, hbd⟩ := hA e he
    have hlt := bond_dist_lt (ell := ell) (M := M) (f := f) (j := j) hell hη hα hsmall
      (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) hbd
    have hc1 : |η| * frobNorm (A e) ≤ 1 := by
      rw [abs_of_pos hη]; linarith
    have := frob_exp_sub_one_le hHT η hc1 _ hexp
    unfold dist1
    rw [abs_of_pos hη] at this
    linarith
  have d1 := key (z, 0) ⟨m0, m1⟩
  have d2 := key (periodicLatticeShift z 0, 1) ⟨m1, m3⟩
  have d3 := key (periodicLatticeShift z 1, 0) ⟨m2, m4⟩
  have d4 := key (z, 1) ⟨m0, m2⟩
  have hp := plaq_gauge g (badU z) z
  rw [plaq_badU z (shift_ne_self z 0 (hN 0)), conj_negOne] at hp
  have hpl : dist1 (plaq (periodicGaugeTransform g (badU z)) z) ≤
      dist1 (periodicGaugeTransform g (badU z) (z, 0)) +
      dist1 (periodicGaugeTransform g (badU z) (periodicLatticeShift z 0, 1)) +
      dist1 (periodicGaugeTransform g (badU z) (periodicLatticeShift z 1, 0)) +
      dist1 (periodicGaugeTransform g (badU z) (z, 1)) := dist1_plaq4 _ _ _ _
  rw [hp, dist1_negOne] at hpl
  have : (1.4 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

#print axioms badU_not_perCubeRegular2

end AdalyFormal.StatementLane2
