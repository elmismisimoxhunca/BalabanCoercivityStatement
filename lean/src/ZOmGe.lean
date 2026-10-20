import ZXR2Wire1

/-!
# ZOmGe -- r5 (5): `OmGe = Ω_j` under `Admissible`  (r4 REPORT §9 / reconciliation A-X4)

`OmGe G j x` (XR2Ops3) reads `x ∈ Ω_j` off the tower geometry `geomOf ell k S`: some `ell^i`-block (`j ≤ i ≤ k`) based at a
point of `Λ_i = {y | ell^i ∣ y, y ∈ Ω_i, y ∉ Ω_{i+1}}` contains `x`.  Here: under `Admissible` (nesting, `Ω_j = ∅` for
`j > k`, `BlockClosed (M·ell^j) Ω_j`) and `0 < ell`, `OmGe (geomOf ell k S) j x ↔ x ∈ S.Om j` for EVERY `j`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem blk_div (q c y x : ℕ) (hq : 0 < q) (hy : q ∣ y) (h1 : y ≤ x) (h2 : x < y + q) :
    y / (q * c) = x / (q * c) := by
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  obtain ⟨t, rfl⟩ := hy
  have hx : x / q = t := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  have hy' : q * t / q = t := Nat.mul_div_cancel_left t hq
  rw [hx, hy']

theorem sub_mod_facts (a q : ℕ) (hq : 0 < q) :
    a - a % q ≤ a ∧ a < a - a % q + q ∧ q ∣ a - a % q := by
  have h1 := Nat.mod_lt a hq
  have h2 := Nat.mod_le a q
  refine ⟨by omega, by omega, Nat.dvd_sub_mod a⟩

theorem om_antitone {Lf : PeriodicLatticeExtent} (S : Tower Lf) (hnest : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j)
    {j i : ℕ} (h : j ≤ i) : S.Om i ⊆ S.Om j := by
  induction i, h using Nat.le_induction with
  | base => exact fun _ h => h
  | succ n _ ih => exact fun x hx => ih (hnest n hx)

theorem omGe_iff_om {Lf : PeriodicLatticeExtent} (ell M R k : ℕ) (hell : 0 < ell) (S : Tower Lf)
    (hS : Admissible ell M R k S) (j : ℕ) (x : PeriodicLatticeSite Lf) :
    OmGe (geomOf ell k S) j x ↔ x ∈ S.Om j := by
  obtain ⟨hnest, hvan, hdvd, hblk, -, -⟩ := hS
  by_cases hjk : k < j
  · rw [hvan j hjk]
    exact ⟨fun h => absurd h (not_OmGe_of_lt (G := geomOf ell k S) hjk x), fun h => h.elim⟩
  · push_neg at hjk
    constructor
    · rintro ⟨i, hji, hik, y, ⟨hydiv, hyOm, -⟩, hxy⟩
      have hq : 0 < ell ^ i := pow_pos hell i
      have hM : x ∈ S.Om i := by
        refine hblk i hik y hyOm x (fun μ => ?_)
        obtain ⟨h1, h2⟩ := hxy μ
        have h2' : (x μ).val < (y μ).val + ell ^ i := h2
        have := blk_div (ell ^ i) M (y μ).val (x μ).val hq (hydiv μ) h1 h2'
        show (x μ).val / (M * ell ^ i) = (y μ).val / (M * ell ^ i)
        rw [mul_comm M]; exact this.symm
      exact om_antitone S hnest hji hM
    · intro hx
      classical
      let P : ℕ → Prop := fun i => x ∈ S.Om i
      let i := Nat.findGreatest P k
      have hP : P i := Nat.findGreatest_spec (P := P) hjk hx
      have hji : j ≤ i := Nat.le_findGreatest hjk hx
      have hik : i ≤ k := Nat.findGreatest_le k
      have hq : 0 < ell ^ i := pow_pos hell i
      have hnot : x ∉ S.Om (i + 1) := by
        by_cases hlt : i < k
        · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self i) hlt
        · have : i = k := le_antisymm hik (not_lt.mp hlt)
          rw [this, hvan (k + 1) (Nat.lt_succ_self k)]
          exact fun h => h.elim
      let y : PeriodicLatticeSite Lf := fun μ => ⟨(x μ).val - (x μ).val % (ell ^ i),
        lt_of_le_of_lt (Nat.sub_le _ _) (x μ).isLt⟩
      have hydiv : ∀ μ, ell ^ i ∣ (y μ).val := by
        intro μ
        exact (sub_mod_facts (x μ).val (ell ^ i) hq).2.2
      have hyx : ∀ μ, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell ^ i := by
        intro μ
        exact (sub_mod_facts (x μ).val (ell ^ i) hq).imp_right (fun h => h.1)
      have hyOm : y ∈ S.Om i := by
        refine hblk i hik x hP y (fun μ => ?_)
        obtain ⟨h1, h2⟩ := hyx μ
        have := blk_div (ell ^ i) M (y μ).val (x μ).val hq (hydiv μ) h1 h2
        show (y μ).val / (M * ell ^ i) = (x μ).val / (M * ell ^ i)
        rw [mul_comm M]; exact this
      have hynot : y ∉ S.Om (i + 1) := by
        intro hy1
        by_cases hlt : i + 1 ≤ k
        · apply hnot
          refine hblk (i + 1) hlt y hy1 x (fun μ => ?_)
          obtain ⟨h1, h2⟩ := hyx μ
          have := blk_div (ell ^ i) (M * ell) (y μ).val (x μ).val hq (hydiv μ) h1 h2
          show (x μ).val / (M * ell ^ (i + 1)) = (y μ).val / (M * ell ^ (i + 1))
          have e : M * ell ^ (i + 1) = ell ^ i * (M * ell) := by ring
          rw [e]; exact this.symm
        · rw [hvan (i + 1) (by omega)] at hy1
          exact hy1
      exact ⟨i, hji, hik, y, ⟨hydiv, hyOm, hynot⟩, hyx⟩

#print axioms omGe_iff_om

end AdalyFormal.IngredientFamilyR2
