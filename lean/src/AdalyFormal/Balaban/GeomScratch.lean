import AdalyFormal.Balaban.CrossSectionField
import AdalyFormal.Balaban.Lemma24Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace GeomScratch

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly

variable {L : PeriodicLatticeExtent}

/-! ## Objects for the per-c -> (geom) assembly. -/

/-- `good(c) = Σ_{x∈Δ'(y,μ)} B(x,μ)²` — the top μ-face longitudinal bond energy. -/
noncomputable def topFaceEnergy (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ :=
  ∑ x ∈ crossSectionTop y ell μ, (B (x, μ)) ^ 2

/-- Block bond energy `Σ_{b⊂B(y)} B(b)²`. -/
noncomputable def blockBondEnergy (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) : ℝ :=
  ∑ b ∈ bondsInBlock y ell, (B b) ^ 2

/-- `boundaryCorr(c) = blockBondEnergy(c₋) + blockBondEnergy(c₊)` — the FULL in-block energy of the
two blocks the coarse bond joins (an over-approximation of Bałaban's actual corrections, which only
makes the per-c inequality easier and the incidence count exact). -/
noncomputable def boundaryCorr (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ :=
  blockBondEnergy B y ell + blockBondEnergy B (coarseShift y ell μ) ell

/-! ## FACT 4 — `Σ_c regionCurlEnergy(c) ≤ slabCurlEnergy`. -/

/-- Total function version of `crossPlaq`: the ordered `(μ,ν)`-plaquette based at `x`. For `μ ≠ ν`
its `curlValue` squares to `xsecCurl²` (`xsecPlaq_sq`), and it lands in `AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs` of `(y,μ)`. -/
noncomputable def xsecPlaq (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    PeriodicLatticePlaquette L :=
  if h : μ < ν then (x, ⟨(μ, ν), h⟩)
  else if h2 : ν < μ then (x, ⟨(ν, μ), h2⟩)
  else (x, ⟨(0, 1), by decide⟩)

theorem xsecPlaq_sq (B : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : μ ≠ ν) :
    xsecCurl B x μ ν ^ 2 = curlValue B (xsecPlaq x μ ν) ^ 2 := by
  unfold xsecCurl xsecPlaq curlValue
  by_cases hlt : μ < ν
  · simp only [hlt, dif_pos]
  · have h2 : ν < μ := lt_of_le_of_ne (not_lt.mp hlt) h.symm
    simp only [hlt, dif_neg, not_false_iff, h2, dif_pos]
    ring

theorem xsecPlaq_base (x : PeriodicLatticeSite L) (μ ν : Fin 3) : (xsecPlaq x μ ν).1 = x := by
  unfold xsecPlaq
  by_cases hlt : μ < ν
  · simp [hlt]
  · by_cases h2 : ν < μ <;> simp [hlt, h2]

theorem xsecPlaq_mem_dirs (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : μ ≠ ν) :
    μ = (xsecPlaq x μ ν).2.1.1 ∨ μ = (xsecPlaq x μ ν).2.1.2 := by
  unfold xsecPlaq
  by_cases hlt : μ < ν
  · simp [hlt]
  · have h2 : ν < μ := lt_of_le_of_ne (not_lt.mp hlt) h.symm
    simp [hlt, h2]

/-- `xsecPlaq x μ ·` is injective on the transverse directions (for fixed `x, μ`): the base recovers
`x` and the direction pair (containing the fixed `μ`) recovers `ν`. -/
theorem xsecPlaq_injOn (x : PeriodicLatticeSite L) (μ : Fin 3) :
    Set.InjOn (fun ν => xsecPlaq x μ ν) (transDirs μ : Set (Fin 3)) := by
  intro ν hν ν' hν' heq
  rw [Finset.mem_coe, mem_transDirs] at hν hν'   -- hν : ν ≠ μ, hν' : ν' ≠ μ
  have heq' : xsecPlaq x μ ν = xsecPlaq x μ ν' := heq
  have hpair := Subtype.ext_iff.mp (congrArg Prod.snd heq')
  unfold xsecPlaq at hpair
  by_cases hlt : μ < ν <;> by_cases hlt' : μ < ν'
  · simp only [hlt, hlt', dif_pos] at hpair
    exact (Prod.ext_iff.mp hpair).2
  · have h2' : ν' < μ := lt_of_le_of_ne (not_lt.mp hlt') hν'
    simp only [hlt, dif_pos, hlt', h2', dif_neg, not_false_iff] at hpair
    exact absurd (Prod.ext_iff.mp hpair).1.symm hν'
  · have h2 : ν < μ := lt_of_le_of_ne (not_lt.mp hlt) hν
    simp only [hlt, h2, dif_neg, not_false_iff, dif_pos, hlt'] at hpair
    exact absurd (Prod.ext_iff.mp hpair).1 hν
  · have h2 : ν < μ := lt_of_le_of_ne (not_lt.mp hlt) hν
    have h2' : ν' < μ := lt_of_le_of_ne (not_lt.mp hlt') hν'
    simp only [hlt, h2, hlt', h2', dif_neg, not_false_iff] at hpair
    exact (Prod.ext_iff.mp hpair).1

/-- **FACT 4, per coarse bond.** `regionCurlEnergy B y ell μ ≤ Σ_{p∈AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs(⟨y,hy⟩,μ)} curlValue²`.
The `(x,ν)`-indexed cross-section curls inject (`xsecPlaq`) into `AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs`, values agreeing by
`xsecPlaq_sq`; the leftover slab plaquettes contribute `≥ 0`. -/
theorem regionCurl_le_slab {ell : ℕ} (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (hy : y ∈ CoarseLattice L ell) :
    regionCurlEnergy B y ell μ ≤ ∑ p ∈ AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs (⟨y, hy⟩, μ), (curlValue B p) ^ 2 := by
  set S := crossSectionTop y ell μ ×ˢ transDirs μ with hSdef
  set Φ : PeriodicLatticeSite L × Fin 3 → PeriodicLatticePlaquette L :=
    fun p => xsecPlaq p.1 μ p.2 with hΦ
  -- regionCurlEnergy = Σ_{p∈S} curlValue(Φ p)²
  have h1 : regionCurlEnergy B y ell μ = ∑ p ∈ S, (curlValue B (Φ p)) ^ 2 := by
    unfold regionCurlEnergy
    rw [← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_product] at hp
    exact xsecPlaq_sq B p.1 μ p.2 (Ne.symm (mem_transDirs.mp hp.2))
  -- Φ is injective on S
  have hinj : Set.InjOn Φ (↑S : Set (PeriodicLatticeSite L × Fin 3)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    have hx : p.1 = q.1 := by
      have := congrArg (·.1) hpq
      simpa [hΦ, xsecPlaq_base] using this
    have hpν := Ne.symm (mem_transDirs.mp hp.2)
    have hqν := Ne.symm (mem_transDirs.mp hq.2)
    have hν : p.2 = q.2 := by
      apply xsecPlaq_injOn p.1 μ (by rw [Finset.mem_coe]; exact hp.2) (by rw [Finset.mem_coe]; exact hq.2)
      simp only [hΦ] at hpq
      rw [hx]; rw [hx] at hpq; exact hpq
    exact Prod.ext hx hν
  -- image ⊆ AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs
  have hsub : S.image Φ ⊆ AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs (⟨y, hy⟩, μ) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hpS, rfl⟩ := hq
    rw [Finset.mem_product] at hpS
    have hxblk : p.1 ∈ blockOf y ell := (mem_crossSectionTop.mp hpS.1).1
    have hpμ := Ne.symm (mem_transDirs.mp hpS.2)
    unfold AdalyFormal.Balaban.Lemma24Assembly.slabPlaqs
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact xsecPlaq_mem_dirs p.1 μ p.2 hpμ
    · rw [hΦ, xsecPlaq_base]; exact hxblk
  rw [h1]
  have hrw : ∑ p ∈ S, (curlValue B (Φ p)) ^ 2
      = ∑ q ∈ S.image Φ, (curlValue B q) ^ 2 :=
    (Finset.sum_image (f := fun q => (curlValue B q) ^ 2) hinj).symm
  rw [hrw]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg _)

/-- **FACT 4, summed.** `Σ_c regionCurlEnergy(c) ≤ slabCurlEnergy`. -/
theorem sum_regionCurl_le_slabCurl {ell : ℕ} (B : Bond L → ℝ) :
    ∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2 ≤ slabCurlEnergy ell B := by
  unfold slabCurlEnergy
  apply Finset.sum_le_sum
  intro c _
  exact regionCurl_le_slab B c.1.1 c.2 c.1.2

/-! ## The reduction — `(geom)` from the per-c bound + incidence FACT 1 (good ≥ Sbet), FACT 2
(boundary ≤ 6·Sin), consuming the proved FACT 4. -/

/-- **(geom) FROM the per-c (2.127)×ell bound and the two incidence sum-facts.** With FACT 4
(`sum_regionCurl_le_slabCurl`) consumed, `(geom)` follows by summing the per-c inequality and the
elementary rearrangement. -/
theorem geom_from_perc {ell : ℕ} (hell2 : 2 ≤ ell) (B : Bond L → ℝ)
    (hPerC : ∀ c : CoarseBond L ell,
      (1 / 3) * (1 / (ell : ℝ) ^ 3) * topFaceEnergy B c.1.1 ell c.2
        ≤ (ell : ℝ) * (lineCoarseRestrict ell B c) ^ 2
          + (1 / (ell : ℝ) ^ 2) * regionCurlEnergy B c.1.1 ell c.2
          + (1 / (ell : ℝ) ^ 2) * boundaryCorr B c.1.1 ell c.2)
    (hF1 : bondNormSq B - inBlockBondEnergy ell B
        ≤ ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2)
    (hF2 : ∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2
        ≤ 6 * inBlockBondEnergy ell B) :
    (ell : ℝ) * coarseQEnergy ell B + (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B
      ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
        - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B := by
  have hc2 : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 2 := by positivity
  have hc3 : (0 : ℝ) ≤ (1 / 3) * (1 / (ell : ℝ) ^ 3) := by positivity
  -- sum the per-c bound
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (CoarseBond L ell))) => hPerC c)
  -- LHS-sum rearrangement
  have hR : ∑ c : CoarseBond L ell,
        ((ell : ℝ) * (lineCoarseRestrict ell B c) ^ 2
          + (1 / (ell : ℝ) ^ 2) * regionCurlEnergy B c.1.1 ell c.2
          + (1 / (ell : ℝ) ^ 2) * boundaryCorr B c.1.1 ell c.2)
      = (ell : ℝ) * coarseQEnergy ell B
        + (1 / (ell : ℝ) ^ 2) * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + (1 / (ell : ℝ) ^ 2) * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl
  have hL : ∑ c : CoarseBond L ell, (1 / 3) * (1 / (ell : ℝ) ^ 3) * topFaceEnergy B c.1.1 ell c.2
      = (1 / 3) * (1 / (ell : ℝ) ^ 3) * (∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2) := by
    rw [← Finset.mul_sum]
  rw [hR, hL] at hsum
  -- the three sum-facts, scaled
  have m1 := mul_le_mul_of_nonneg_left hF1 hc3
  have m2 := mul_le_mul_of_nonneg_left hF2 hc2
  have m4 := mul_le_mul_of_nonneg_left (sum_regionCurl_le_slabCurl (ell := ell) B) hc2
  linarith [hsum, m1, m2, m4]

/-! ## FACT 2 — `Σ_c boundaryCorr(c) ≤ 6·inBlockBondEnergy`. -/

/-- `periodicLatticeShift · μ` is injective. -/
theorem periodicLatticeShift_injective (μ : Fin 3) :
    Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) := by
  intro x x' h
  funext ν
  by_cases hν : ν = μ
  · subst hν
    have hc : periodicLatticeShift x ν ν = periodicLatticeShift x' ν ν := congrFun h ν
    rw [periodicLatticeShift_self, periodicLatticeShift_self] at hc
    exact add_right_cancel hc
  · have hc : periodicLatticeShift x μ ν = periodicLatticeShift x' μ ν := congrFun h ν
    unfold periodicLatticeShift at hc
    rwa [Function.update_of_ne hν, Function.update_of_ne hν] at hc

/-- `coarseShift · ell μ` is injective (iterate of an injective map). -/
theorem coarseShift_injective {ell : ℕ} (μ : Fin 3) :
    Function.Injective (fun y : PeriodicLatticeSite L => coarseShift y ell μ) := by
  have he : (fun y : PeriodicLatticeSite L => coarseShift y ell μ)
      = (fun z => periodicLatticeShift z μ)^[ell] := by funext y; rfl
  rw [he]
  exact (periodicLatticeShift_injective μ).iterate ell

theorem blockBondEnergy_nonneg (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) :
    0 ≤ blockBondEnergy B y ell :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- `inBlockBondEnergy = Σ_{y∈Λ'} blockBondEnergy(y)`. -/
theorem inBlockBondEnergy_eq_sum (ell : ℕ) (B : Bond L → ℝ) :
    inBlockBondEnergy ell B = ∑ y ∈ CoarseLattice L ell, blockBondEnergy B y ell := rfl

/-- Per direction `μ`: shifting the coarse centre keeps the total in-block energy `≤ Sin`. -/
theorem sum_shift_blockBondEnergy_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : Bond L → ℝ) (μ : Fin 3) :
    ∑ y ∈ CoarseLattice L ell, blockBondEnergy B (coarseShift y ell μ) ell
      ≤ inBlockBondEnergy ell B := by
  rw [inBlockBondEnergy_eq_sum]
  rw [← Finset.sum_image (f := fun z => blockBondEnergy B z ell)
      (s := CoarseLattice L ell) (g := fun y => coarseShift y ell μ)
      (coarseShift_injective μ).injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact coarseShift_mem_coarseLattice hdvd hy μ
  · exact fun z _ _ => blockBondEnergy_nonneg B z ell

/-- **FACT 2.** `Σ_c boundaryCorr(c) ≤ 6·inBlockBondEnergy`. Each block is `c₋` for exactly 3 coarse
bonds (`3·Sin`) and `c₊` for exactly 3 (`≤ 3·Sin` via the `coarseShift` reindexing). -/
theorem sum_boundaryCorr_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → ℝ) :
    ∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2 ≤ 6 * inBlockBondEnergy ell B := by
  rw [Fintype.sum_prod_type]
  simp only [boundaryCorr]
  -- split the inner sum over μ
  have hsplit : ∀ y : {y // y ∈ CoarseLattice L ell},
      ∑ μ : Fin 3, (blockBondEnergy B y.1 ell + blockBondEnergy B (coarseShift y.1 ell μ) ell)
        = 3 * blockBondEnergy B y.1 ell
          + ∑ μ : Fin 3, blockBondEnergy B (coarseShift y.1 ell μ) ell := by
    intro y
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib]
  -- term A = 3·Sin
  have hA : ∑ y : {y // y ∈ CoarseLattice L ell}, 3 * blockBondEnergy B y.1 ell
      = 3 * inBlockBondEnergy ell B := by
    rw [← Finset.mul_sum, inBlockBondEnergy_eq_sum]
    congr 1
    exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
      (fun z => blockBondEnergy B z ell)).symm
  -- term B ≤ 3·Sin
  have hB : ∑ y : {y // y ∈ CoarseLattice L ell},
        ∑ μ : Fin 3, blockBondEnergy B (coarseShift y.1 ell μ) ell
      ≤ 3 * inBlockBondEnergy ell B := by
    rw [Finset.sum_comm]
    calc ∑ μ : Fin 3, ∑ y : {y // y ∈ CoarseLattice L ell},
            blockBondEnergy B (coarseShift y.1 ell μ) ell
        = ∑ μ : Fin 3, ∑ y ∈ CoarseLattice L ell, blockBondEnergy B (coarseShift y ell μ) ell := by
          apply Finset.sum_congr rfl; intro μ _
          exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
            (fun z => blockBondEnergy B (coarseShift z ell μ) ell)).symm
      _ ≤ ∑ _μ : Fin 3, inBlockBondEnergy ell B :=
          Finset.sum_le_sum (fun μ _ => sum_shift_blockBondEnergy_le hdvd B μ)
      _ = 3 * inBlockBondEnergy ell B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [hA]; linarith [hB]

/-! ## FACT 1 — `∑_c topFaceEnergy(c) = bondNormSq − inBlockBondEnergy` (= Sbet), hence `≥`.

Each fine bond `b = (x,ν)` has its base site `x` in a UNIQUE block `B(y)` (`coarseLattice_exists`
+ `coarseLattice_unique`). Within that block, `b` is either **in-block** (`shift x ν` also in `B(y)`)
or **cross-block** (top μ-face bond). The dichotomy `shift_notMem_iff_top` is EXACTLY
`shift x ν ∉ B(y) ↔ x_ν = y_ν + (ell−1)` (`x` on the top ν-layer) — the torus-wrap edge case
`x_ν = L_ν` is ruled out of "in-block" by `hstrict` (`ell < L_ν+1`, so a block never wraps the axis).
So the bonds based in `B(y)` split as `bondsInBlock y ⊔ (⊔_μ crossSectionTop y ell μ)`, giving the
exact partition `bondNormSq = inBlockBondEnergy + ∑_c topFaceEnergy`. -/

/-- The bonds whose BASE site lies in the block `B(y)` — `{b : b.1 ∈ blockOf y}`. As `y` ranges over
`Λ'` these partition all bonds (each base site is in a unique block). -/
def bondsBasedIn (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (Bond L) :=
  Finset.univ.filter (fun b : Bond L => b.1 ∈ blockOf y ell)

/-- **The in-block/cross-block dichotomy.** For a coarse centre `y` (whose block fits, `hstrict`
excluding the axis-wrapping single-block case) and a block site `x`, the ν-shift leaves the block iff
`x` is on the top ν-layer `x_ν = y_ν + (ell−1)`. This is the geometric heart of FACT 1. -/
theorem shift_notMem_iff_top {ell : ℕ} (_hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {y x : PeriodicLatticeSite L} (ν : Fin 3)
    (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell) :
    periodicLatticeShift x ν ∉ blockOf y ell ↔ (x ν).val = (y ν).val + (ell - 1) := by
  have hfitν := coarseLattice_mem_fits hdvd hy ν
  have hstrictν := hstrict ν
  rw [mem_blockOf] at hx
  have hxν := hx ν
  have hshift1 : periodicLatticeShift x ν = coarseShift x 1 ν := by
    unfold coarseShift; rw [Function.iterate_one]
  have hsval : ((periodicLatticeShift x ν) ν).val = ((x ν).val + 1) % (L ν + 1) := by
    rw [hshift1, coarseShift_val_eq]
  rw [mem_blockOf]
  constructor
  · intro hnot
    by_contra hne
    apply hnot
    intro ρ
    by_cases hρ : ρ = ν
    · subst hρ
      have hlt : (x ρ).val + 1 < L ρ + 1 := by omega
      refine ⟨?_, ?_⟩ <;> rw [hsval, Nat.mod_eq_of_lt hlt] <;> omega
    · rw [show (periodicLatticeShift x ν) ρ = x ρ from Function.update_of_ne hρ _ _]
      exact hx ρ
  · intro htop hmem
    have hmemν := hmem ν
    rw [hsval] at hmemν
    rcases eq_or_lt_of_le hfitν with heq | hlt
    · -- y_ν + ell = L_ν + 1 : shifted ν-coord wraps to 0
      have hx1 : (x ν).val + 1 = L ν + 1 := by omega
      rw [hx1, Nat.mod_self] at hmemν
      omega
    · -- y_ν + ell < L_ν + 1 : no wrap, shifted = x_ν+1 = y_ν+ell, not < y_ν+ell
      have hx1 : (x ν).val + 1 < L ν + 1 := by omega
      rw [Nat.mod_eq_of_lt hx1] at hmemν
      omega

/-- **The per-block split.** `∑_{b : b.1∈B(y)} B(b)² = ∑_{b⊂B(y)} B(b)² + ∑_μ topFaceEnergy(y,μ)`:
the bonds based in `B(y)` are the in-block bonds together with the top-face bonds in each direction. -/
theorem bondsBasedIn_split {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (B : Bond L → ℝ) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    ∑ b ∈ bondsBasedIn y ell, (B b) ^ 2
      = ∑ b ∈ bondsInBlock y ell, (B b) ^ 2 + ∑ μ : Fin 3, topFaceEnergy B y ell μ := by
  rw [← Finset.sum_filter_add_sum_filter_not (bondsBasedIn y ell) (fun b => bondInBlock y ell b)]
  congr 1
  · -- in-block part
    congr 1
    ext b
    simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and, bondsInBlock]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1, h⟩
  · -- top-face part = ∑_μ topFaceEnergy
    have hset : (bondsBasedIn y ell).filter (fun b => ¬ bondInBlock y ell b)
        = Finset.univ.filter (fun b : Bond L => b.1 ∈ crossSectionTop y ell b.2) := by
      ext b
      simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and, mem_crossSectionTop,
        bondInBlock]
      constructor
      · rintro ⟨hbase, hnib⟩
        refine ⟨hbase, ?_⟩
        have hns : periodicLatticeShift b.1 b.2 ∉ blockOf y ell := fun hs => hnib ⟨hbase, hs⟩
        exact (shift_notMem_iff_top hell hdvd hstrict b.2 hy hbase).mp hns
      · rintro ⟨hbase, htop⟩
        refine ⟨hbase, ?_⟩
        intro hib
        have hns := hib.2
        have := (shift_notMem_iff_top hell hdvd hstrict b.2 hy hbase).mpr htop
        exact this hns
    rw [hset]
    -- ∑_{b : b.1∈crossSectionTop y ell b.2} B(b)² = ∑_μ ∑_{x∈crossSectionTop y ell μ} B(x,μ)²
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    dsimp only
    rw [Finset.sum_ite_mem, Finset.univ_inter, topFaceEnergy]

/-- **FACT 1 (equality).** `bondNormSq = inBlockBondEnergy + ∑_c topFaceEnergy`. The bonds based in
each block partition all bonds; the per-block split then separates in-block from top-face. -/
theorem sum_topFace_eq_Sbet {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (B : Bond L → ℝ) :
    bondNormSq B
      = inBlockBondEnergy ell B + ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2 := by
  -- Step A: partition all bonds by owning block
  have hdisj : (↑(CoarseLattice L ell) : Set (PeriodicLatticeSite L)).PairwiseDisjoint
      (fun y => bondsBasedIn y ell) := by
    intro y hy y' hy' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro b hby hby'
    simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and] at hby hby'
    exact hne (coarseLattice_unique ell (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hy') hby hby')
  have hcover : (Finset.univ : Finset (Bond L))
      = (CoarseLattice L ell).biUnion (fun y => bondsBasedIn y ell) := by
    ext b
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
    obtain ⟨y, hymem, hyblk⟩ := coarseLattice_exists ell hell hdvd b.1
    exact ⟨y, hymem, by simp only [bondsBasedIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact hyblk⟩
  have hStepA : bondNormSq B = ∑ y ∈ CoarseLattice L ell, ∑ b ∈ bondsBasedIn y ell, (B b) ^ 2 := by
    unfold bondNormSq
    rw [hcover, Finset.sum_biUnion hdisj]
  rw [hStepA]
  -- Step B: per-block split, then sum over y
  rw [Finset.sum_congr rfl (fun y hy => bondsBasedIn_split hell hdvd hstrict B hy)]
  rw [Finset.sum_add_distrib]
  -- congr 1 auto-discharges the in-block goal (definitional); only the top-face sum remains
  congr 1
  -- ∑_y ∑_μ topFaceEnergy = ∑_c topFaceEnergy
  rw [Fintype.sum_prod_type]
  exact Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
    (fun y => ∑ μ : Fin 3, topFaceEnergy B y ell μ)

/-- **FACT 1**, in the form `geom_from_perc` consumes: `Sbet ≤ ∑_c topFaceEnergy`. -/
theorem sum_topFace_ge_Sbet {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (B : Bond L → ℝ) :
    bondNormSq B - inBlockBondEnergy ell B
      ≤ ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2 := by
  have h := sum_topFace_eq_Sbet hell hdvd hstrict B
  linarith [h]

/-! ## The reduction of `Lemma24Conclusion` to the SINGLE remaining per-`c` bound.

With FACT 1 (`sum_topFace_ge_Sbet`), FACT 2 (`sum_boundaryCorr_le`), FACT 4
(`sum_regionCurl_le_slabCurl`, consumed inside `geom_from_perc`) all kernel-proved, the entire
remaining gap between the proved chain and an UNCONDITIONAL `Lemma24Conclusion` at `ell ∈ {2,3}` is
the single per-coarse-bond analytic bound `hPerC`. `lemma24_from_perC` is kernel-clean and takes
`hPerC` as its ONLY unproved input; discharging `hPerC` (the per-`c` cross-sectional operator
positivity, feeders `crossSection_2124` + `cross_section_2125c` + `block_operator_gap`) makes the
milestone unconditional. -/

/-- **`Lemma24Conclusion` from the per-`c` bound alone.** All the incidence combinatorics
(FACT 1/2/4), the slab-curl multiplicity identity, and the `(star)`/`(geom)` reductions are
kernel-proved; the sole remaining hypothesis is `hPerC`, the per-coarse-bond `(2.127)×ell`
inequality. `admissibleSubspaceInter`/`hstrict`/`hdvd` are the binding-regime data (`(geom)` is
vacuous off it). -/
theorem lemma24_from_perC {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (hPerC : ∀ c : CoarseBond L ell,
      (1 / 3) * (1 / (ell : ℝ) ^ 3) * topFaceEnergy B c.1.1 ell c.2
        ≤ (ell : ℝ) * (lineCoarseRestrict ell B c) ^ 2
          + (1 / (ell : ℝ) ^ 2) * regionCurlEnergy B c.1.1 ell c.2
          + (1 / (ell : ℝ) ^ 2) * boundaryCorr B c.1.1 ell c.2) :
    Lemma24Conclusion ell B := by
  have hell0 : 0 < ell := by omega
  have hGeom := geom_from_perc hell2 B hPerC
    (sum_topFace_ge_Sbet hell0 hdvd hstrict B)
    (sum_boundaryCorr_le hdvd B)
  exact lemma24_from_geom hell2 (hstrict 0) (hstrict 1) (hstrict 2) hdvd B hB hGeom

#print axioms regionCurl_le_slab
#print axioms sum_regionCurl_le_slabCurl
#print axioms geom_from_perc
#print axioms sum_boundaryCorr_le
#print axioms shift_notMem_iff_top
#print axioms bondsBasedIn_split
#print axioms sum_topFace_eq_Sbet
#print axioms sum_topFace_ge_Sbet
#print axioms lemma24_from_perC

end GeomScratch
