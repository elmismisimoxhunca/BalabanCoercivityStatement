import ZR2D
import AdalyFormal.Balaban.BlockedGaugeCore

/-!
# R3A1 -- combinatorics for `||Q_k(U)|| <= 1`:
shift injectivity, block disjointness for the embedded coarse lattice, the block-sum <= full-sum estimate.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.StatementLane2 (embSite embSite_inj)

theorem shift_injective {L : PeriodicLatticeExtent} (μ : Fin 3) :
    Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) := by
  intro x y h
  funext ν
  have h' := congrFun h ν
  simp only [periodicLatticeShift] at h'
  by_cases hν : ν = μ
  · subst hν
    simp only [Function.update_self] at h'
    exact add_right_cancel h'
  · simpa [Function.update_of_ne hν] using h'

theorem pathSite_injective {L : PeriodicLatticeExtent} (μ : Fin 3) (i : ℕ) :
    Function.Injective (fun x : PeriodicLatticeSite L => pathSite x μ i) := by
  unfold pathSite
  exact (shift_injective μ).iterate i

/-- blocks of the embedded coarse lattice are pairwise disjoint -/
theorem block_unique (ell : ℕ) (hell : 0 < ell) (k : ℕ) {Lu : PeriodicLatticeExtent}
    {y1 y2 : PeriodicLatticeSite Lu} {x : PeriodicLatticeSite (AdalyFormal.StatementLane.scaleUp ell k Lu)}
    (h1 : x ∈ blockOf (embSite ell hell k y1) (ell ^ k))
    (h2 : x ∈ blockOf (embSite ell hell k y2) (ell ^ k)) : y1 = y2 := by
  rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf] at h1 h2
  funext μ
  apply Fin.ext
  have a1 := h1 μ
  have a2 := h2 μ
  simp only [embSite] at a1 a2
  have hn : 0 < ell ^ k := pow_pos hell k
  have e1 : (x μ).val / (ell ^ k) = (y1 μ).val :=
    Nat.div_eq_of_lt_le (by nlinarith [a1.1]) (by nlinarith [a1.2])
  have e2 : (x μ).val / (ell ^ k) = (y2 μ).val :=
    Nat.div_eq_of_lt_le (by nlinarith [a2.1]) (by nlinarith [a2.2])
  omega

/-- `∑_{y'} ∑_{x ∈ B(emb y')} g x ≤ ∑_x g x` for `g ≥ 0` -/
theorem block_sum_le (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (g : PeriodicLatticeSite (AdalyFormal.StatementLane.scaleUp ell k Lu) → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ y : PeriodicLatticeSite Lu, ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k), g x
      ≤ ∑ x, g x := by
  classical
  have h1 : ∀ y : PeriodicLatticeSite Lu, ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k), g x
      = ∑ x, if x ∈ blockOf (embSite ell hell k y) (ell ^ k) then g x else 0 := by
    intro y
    rw [← Finset.sum_filter]
    congr 1
    ext x; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.sum_filter]
  by_cases h : ∃ y, x ∈ blockOf (embSite ell hell k y) (ell ^ k)
  · obtain ⟨y0, hy0⟩ := h
    have : Finset.univ.filter (fun y : PeriodicLatticeSite Lu =>
        x ∈ blockOf (embSite ell hell k y) (ell ^ k)) = {y0} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hy; exact block_unique ell hell k hy hy0
      · rintro rfl; exact hy0
    rw [this]; simp
  · push_neg at h
    have : Finset.univ.filter (fun y : PeriodicLatticeSite Lu =>
        x ∈ blockOf (embSite ell hell k y) (ell ^ k)) = ∅ := by
      ext y; simp [h y]
    rw [this]; simp [hg x]

theorem sum_comp_pathSite_le {L : PeriodicLatticeExtent} (μ : Fin 3) (i : ℕ)
    (f : PeriodicLatticeSite L → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x, f (pathSite x μ i) ≤ ∑ z, f z := by
  classical
  have hinj := pathSite_injective (L := L) μ i
  have hbij : Function.Bijective (fun x : PeriodicLatticeSite L => pathSite x μ i) :=
    Finite.injective_iff_bijective.mp hinj
  exact le_of_eq (Equiv.sum_comp (Equiv.ofBijective _ hbij) f)

#print axioms shift_injective
#print axioms block_unique
#print axioms block_sum_le
#print axioms sum_comp_pathSite_le

end AdalyFormal.StatementLane3
