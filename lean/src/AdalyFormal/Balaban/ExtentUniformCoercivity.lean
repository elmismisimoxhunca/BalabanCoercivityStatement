/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FibreAggregate
import AdalyFormal.Balaban.WitnessInequality
import AdalyFormal.Balaban.BridgeInverseCarrier
import AdalyFormal.Balaban.IslandBridge
import AdalyFormal.Balaban.DeltaPrimeOperator

set_option autoImplicit false

/-!
# `ExtentUniformCoercivity` — the fibre bound carried to the WHOLE space, `L`-free

`FibreAggregate.aggregate_fibre_bound` is an `L`-FREE coercivity bound (`γ_agg = 1/3316224`, every
factor counted) that holds only ON THE FIBRE `{Q A = 0}`. The tower's first rung wants a WHOLE-SPACE
bound with a constant independent of the lattice extent. This module carries the fibre bound off the
fibre and states exactly what that costs.

## What is proved

1. **§1 — the lift is INVISIBLE to `P_Ax`.** `FullySupplied.suTwoLift 2` (the exact right inverse of
   `Q` at `U = 1`, already used by `qCLM_surjective_trivialU`) is supported on the ODD layer of each
   direction, and every bond of a staircase path `Γ_{y,x}` from a COARSE corner has its base
   coordinate, in its own direction, equal to `y`'s — hence EVEN. So `pAx (suTwoLift 2 F) = 0` and
   `pAx (A − suTwoLift 2 F) = pAx A` EXACTLY: the gauge-fixing slot contributes no cross term at
   all.
2. **§2 — the lift's energy is `L`-free**: `bondEnergy (suTwoLift 2 F) ≤ 32 · coarseEnergy F`,
   `32 = ell² · card B(y) = 4 · 8`.
3. **§3 — `master_defect_bound`**, the theorem:

       bondEnergy A ≤ 13264896 · (curlEnergy A + P_Ax A) + 13583253568 · ‖Q A‖²

   for EVERY whole-space `A` and every extent with `2 ∣ (L μ + 1)`.
   `13264896 = 4 · 3316224`; `13583253568 = 4096 · 3316224 + 64`.
4. **§4 — `extent_uniform_whole_space`**: `γ_ext a · bondEnergy A ≤ curlEnergy A + P_Ax A +
   a‖QA‖²` with `γ_ext a = min(1/13264896, a/13583253568)` fixed BEFORE the extent is quantified
   (`extent_uniform_exists` is the `∃ γ, ∀ L` form; the vacuous shape would be `∀ L, ∃ γ`).
5. **§5 — the adapter**, the same inequality at `deltaKCLMNormalized (trivialU L)`,
   `pAxCLM (CoarseLattice L 2) 2`, `qCLM (trivialU L) 2` — literally the shape
   `TowerOneStep.Rung.gf_of_defect` takes as `hdef`. This module does NOT import `TowerOneStep`:
   §3/§4 are stated against the tree's bare `curlEnergy`/`pAx`/`lineCoarseRestrictCov`, so they
   survive any re-targeting of the rung, and §5 is a severable re-expression.
6. **§6 — the `‖QA‖²` term is NOT removable.** Choosing the coarse mode supported on direction `0`,
   the lift is also CURL-FREE, so it is a nonzero whole-space field with
   `curlEnergy = P_Ax = 0`. Hence `γ‖x‖² ≤ ⟨x,Δ_k(1)x⟩ + ⟨x,P_Ax x⟩` is UNSATISFIABLE for every
   `γ > 0` at these operators (`un_augmented_coercivity_false`), and no constant `K` whatever makes
   the two-term bound true (`no_constant_without_Q_term`). Consequently the `γ₀ − C‖Q‖²` conversion
   can never be positive here (`gf_of_defect_yields_nothing_here`).

## Scope, stated plainly

* `ell = 2`, flat background `U = 1`, periodic extents with `2 ∣ (L μ + 1)`. The curved transfer is
  `CovariantFibreTransfer`'s business and is not attempted here.
* `P` throughout is the tree's own CMP95 `(1.10)` axial form `pAx`/`pAxCLM`. CMP99b `(3.128)`'s
  gauge-fixing term is `‖RD*·‖²`, a DIFFERENT object this tree does not build; §6 is not a statement
  about that `P`, and nothing here claims Bałaban's hypothesis is false.
* What §6 does settle: the campaign's currently available `(Δ, P)` pair cannot supply an
  un-augmented whole-space bound, so the `a‖Qx‖²` slot of `M = Δ + P + Q*aQ` is load-bearing.
* The `a`-augmented bound proved here is what `M`-coercivity consumes; it is NOT the un-taxed
  `hDP` of the current `Rung`, and no iterated/tower consequence is drawn in this module.
-/

namespace AdalyFormal.Balaban.ExtentUniformCoercivity

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite PeriodicLatticeEdge PeriodicLatticePlaquette periodicLatticeShift)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice staircasePath axisSegment mem_axisSegment)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictSuTwo
  lineCoarseRestrictCov_trivialU lineCoarseRestrictCov_add)
open AdalyFormal.Balaban.FullySupplied (suTwoLift lineCoarseRestrictSuTwo_suTwoLift)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy bondEnergy_nonneg
  plaqEnergy_nonneg)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue flatCurlValue_add flatCurlValue_smul)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg cc cc_val cc_even cc_mem
  deltaK_trivialU_eq_curlEnergy sq_two plaq_dirs zeroSite zeroSite_val)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAxBlock pathIntegral pAx_nonneg pAxCLM
  inner_pAxCLM_eq)
open AdalyFormal.Balaban.FibreAggregate (sum_over_blocks mem_blockOf_iff_cc card_blockOf_two_le
  aggregate_fibre_bound bondEnergy_pos witL3 hdvd_witL3 hdvd_witL5' card_bond_differs
  card_bond_witL3 card_bond_witL5)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.WitnessInequality (plaqEnergy_flatCurl_le)
open AdalyFormal.Balaban.BridgeInverse (qCLM qstarCLM CoarseFnL2 qCLM_apply qCLM_hadj qCLM_le
  fineCLM fineCLM_inner injective_of_coercive)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.IslandBridge (norm_sq_bondFnL2)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE STAIRCASE PATH NEVER TOUCHES A LAST-LAYER BOND

`Γ_{y,x}` is walked from a COARSE corner `y` to a site of its own block. Each of its three axis
segments constrains the bond's base coordinate IN ITS OWN DIRECTION to the half-open interval
`[y_μ, x_μ)`, and `x ∈ B(y)` at `ell = 2` forces `x_μ ≤ y_μ + 1`. So that coordinate equals `y_μ`,
which is EVEN. `suTwoLift 2` is supported exactly on the ODD layer. Hence the lift is invisible to
`P_Ax` — not small, ZERO. -/

/-- Every bond of `Γ_{y,x}` has base coordinate, in its own direction, equal to `y`'s. -/
theorem staircase_bond_coord_eq {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y 2)
    {e : Bond L} (he : e ∈ staircasePath y x) : (e.1 e.2).val = (y e.2).val := by
  have hb := mem_blockOf.1 hx
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at he
  rcases he with (he | he) | he
  · obtain ⟨hdir, -, hlo, hhi⟩ := mem_axisSegment.1 he
    obtain ⟨h1, h2⟩ := hb 2
    rw [hdir]; omega
  · obtain ⟨hdir, -, hlo, hhi⟩ := mem_axisSegment.1 he
    obtain ⟨h1, h2⟩ := hb 1
    rw [hdir]; omega
  · obtain ⟨hdir, -, hlo, hhi⟩ := mem_axisSegment.1 he
    obtain ⟨h1, h2⟩ := hb 0
    rw [hdir]; omega

/-- The lift vanishes on every bond of every in-block staircase path from a coarse corner. -/
theorem suTwoLift_eq_zero_on_staircase (F : CoarseBond L 2 → SuTwo)
    {y x : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (hx : x ∈ blockOf y 2) {e : Bond L} (he : e ∈ staircasePath y x) :
    suTwoLift 2 F e = 0 := by
  have hco := staircase_bond_coord_eq hx he
  have hpar := hy e.2
  unfold suTwoLift
  rw [if_neg]
  omega

/-- Consequently the path integral of the lift vanishes. -/
theorem pathIntegral_suTwoLift (F : CoarseBond L 2 → SuTwo)
    {y x : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (hx : x ∈ blockOf y 2) : pathIntegral (suTwoLift 2 F) y x = 0 := by
  unfold pathIntegral
  exact Finset.sum_eq_zero fun e he => suTwoLift_eq_zero_on_staircase F hy hx he

/-- **THE GAUGE-FIXING SLOT SEES NOTHING.** Subtracting the lift does not change a single path
integral, so `P_Ax` is unchanged EXACTLY (no `2ε`-splitting, no cross term). -/
theorem pathIntegral_sub_suTwoLift (A : Bond L → SuTwo) (F : CoarseBond L 2 → SuTwo)
    {y x : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (hx : x ∈ blockOf y 2) :
    pathIntegral (fun b => A b - suTwoLift 2 F b) y x = pathIntegral A y x := by
  unfold pathIntegral
  refine Finset.sum_congr rfl fun e he => ?_
  show A e - suTwoLift 2 F e = A e
  rw [suTwoLift_eq_zero_on_staircase F hy hx he, sub_zero]

/-- `P_Ax` of the lift is `0` over ANY set of COARSE centers. Stated for a general `S` because the
source uses two: CMP95 `(1.10)`'s full `CoarseLattice L 2` and CMP96 `(2.121)` / CMP99b `(3.156)`'s
restricted sub-`Finset` `Λ'` (`AxialCoercivity.pAx`'s own docstring records both). -/
theorem pAx_suTwoLift_of_coarse (F : CoarseBond L 2 → SuTwo) (S : Finset (PeriodicLatticeSite L))
    (hS : ∀ y ∈ S, ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    pAx (suTwoLift (L := L) 2 F) S 2 = 0 := by
  unfold pAx
  refine Finset.sum_eq_zero fun y hy => ?_
  unfold pAxBlock
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [pathIntegral_suTwoLift F (hS y hy) (Finset.mem_of_mem_erase hx), norm_zero]
  norm_num

/-- `P_Ax` of the lift is `0` on the CMP95 `(1.10)` center set. -/
theorem pAx_suTwoLift (F : CoarseBond L 2 → SuTwo) :
    pAx (suTwoLift (L := L) 2 F) (CoarseLattice L 2) 2 = 0 :=
  pAx_suTwoLift_of_coarse F _ fun _ hy => mem_CoarseLattice.1 hy

/-- `P_Ax` is unchanged by removing the lift — over any set of coarse centers. -/
theorem pAx_sub_suTwoLift_of_coarse (A : Bond L → SuTwo) (F : CoarseBond L 2 → SuTwo)
    (S : Finset (PeriodicLatticeSite L)) (hS : ∀ y ∈ S, ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    pAx (fun b => A b - suTwoLift 2 F b) S 2 = pAx A S 2 := by
  unfold pAx
  refine Finset.sum_congr rfl fun y hy => ?_
  unfold pAxBlock
  exact Finset.sum_congr rfl fun x hx => by
    rw [pathIntegral_sub_suTwoLift A F (hS y hy) (Finset.mem_of_mem_erase hx)]

/-- `P_Ax` is unchanged by removing the lift. -/
theorem pAx_sub_suTwoLift (A : Bond L → SuTwo) (F : CoarseBond L 2 → SuTwo) :
    pAx (fun b => A b - suTwoLift 2 F b) (CoarseLattice L 2) 2 = pAx A (CoarseLattice L 2) 2 :=
  pAx_sub_suTwoLift_of_coarse A F _ fun _ hy => mem_CoarseLattice.1 hy

#print axioms staircase_bond_coord_eq
#print axioms suTwoLift_eq_zero_on_staircase
#print axioms pAx_suTwoLift_of_coarse
#print axioms pAx_suTwoLift
#print axioms pAx_sub_suTwoLift_of_coarse
#print axioms pAx_sub_suTwoLift

/-! ## §2 — THE LIFT'S ENERGY IS `L`-FREE

`32 = 4 · 8`: `4 = ell²` is the lift's own weight `(ell : ℝ) • F`, and `8` is
`FibreAggregate.card_blockOf_two_le` — the number of fine sites in one side-`2` block. Neither
factor mentions the extent. -/

/-- The coarse `L²` energy — the explicit sum, so no carrier convention is smuggled in. -/
noncomputable def coarseEnergy (F : CoarseBond L 2 → SuTwo) : ℝ :=
  ∑ c : CoarseBond L 2, ‖F c‖ ^ 2

theorem coarseEnergy_nonneg (F : CoarseBond L 2 → SuTwo) : 0 ≤ coarseEnergy F :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The block-corner map, on bonds. -/
def ccB (b : Bond L) : CoarseBond L 2 := (⟨cc b.1, cc_mem b.1⟩, b.2)

/-- **Each coarse bond has at most `8` fine bonds over it.** The fibre injects into the block
`B(y)`, whose cardinality is `card_blockOf_two_le`'s `8`. -/
theorem fibre_card_le (c : CoarseBond L 2) :
    ((Finset.univ : Finset (Bond L)).filter (fun b => ccB b = c)).card ≤ 8 := by
  classical
  have hc : ∀ μ : Fin 3, ((c.1 : PeriodicLatticeSite L) μ).val % 2 = 0 :=
    mem_CoarseLattice.1 c.1.2
  refine le_trans (Finset.card_le_card_of_injOn (fun b : Bond L => b.1) ?_ ?_)
    (card_blockOf_two_le (c.1 : PeriodicLatticeSite L))
  · intro b hb
    have h : ccB b = c := (Finset.mem_filter.1 hb).2
    have h1 : cc b.1 = (c.1 : PeriodicLatticeSite L) :=
      congrArg (fun z : CoarseBond L 2 => (z.1 : PeriodicLatticeSite L)) h
    exact (mem_blockOf_iff_cc hc b.1).2 h1
  · intro b hb b' hb' hEq
    have h : ccB b = c := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
    have h' : ccB b' = c := (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).2
    have h2 : b.2 = b'.2 := by
      have e1 : (ccB b).2 = c.2 := congrArg Prod.snd h
      have e2 : (ccB b').2 = c.2 := congrArg Prod.snd h'
      exact e1.trans e2.symm
    exact Prod.ext hEq h2

/-- **Fibrewise summation with the counted multiplicity `8`.** -/
theorem sum_comp_ccB_le (h : CoarseBond L 2 → ℝ) (hnn : ∀ c, 0 ≤ h c) :
    ∑ b : Bond L, h (ccB b) ≤ 8 * ∑ c : CoarseBond L 2, h c := by
  classical
  have hmaps : ∀ b ∈ (Finset.univ : Finset (Bond L)),
      ccB b ∈ (Finset.univ : Finset (CoarseBond L 2)) := fun b _ => Finset.mem_univ _
  have key := Finset.sum_fiberwise_of_maps_to hmaps (fun b : Bond L => h (ccB b))
  rw [← key, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hconst : (∑ b ∈ (Finset.univ : Finset (Bond L)).filter (fun b => ccB b = c), h (ccB b))
      = (((Finset.univ : Finset (Bond L)).filter (fun b => ccB b = c)).card : ℝ) * h c := by
    rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.1 hb).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [hconst]
  have hcard : (((Finset.univ : Finset (Bond L)).filter (fun b => ccB b = c)).card : ℝ) ≤ 8 := by
    exact_mod_cast fibre_card_le c
  nlinarith [hnn c]

/-- **THE LIFT'S ENERGY BOUND.** `bondEnergy (𝒬⁻¹F) ≤ 32 · coarseEnergy F`, no `L`. -/
theorem bondEnergy_suTwoLift_le (F : CoarseBond L 2 → SuTwo) :
    bondEnergy (suTwoLift (L := L) 2 F) ≤ 32 * coarseEnergy F := by
  have hpt : ∀ b : Bond L, ‖suTwoLift 2 F b‖ ^ 2 ≤ 4 * ‖F (ccB b)‖ ^ 2 := by
    intro b
    unfold suTwoLift
    by_cases hb : (b.1 b.2).val % 2 = 2 - 1
    · rw [if_pos hb]
      have heq : F (⟨AdalyFormal.Balaban.QcEquation.blockCorner 2 b.1,
          AdalyFormal.Balaban.QcEquation.blockCorner_mem b.1⟩, b.2) = F (ccB b) := rfl
      rw [heq, norm_smul, mul_pow]
      have h2 : ‖((2 : ℕ) : ℝ)‖ ^ 2 = 4 := by
        rw [Real.norm_eq_abs]; norm_num
      rw [h2]
    · rw [if_neg hb, norm_zero, show (0 : ℝ) ^ 2 = 0 from by norm_num]
      positivity
  calc bondEnergy (suTwoLift (L := L) 2 F) = ∑ b : Bond L, ‖suTwoLift 2 F b‖ ^ 2 := rfl
    _ ≤ ∑ b : Bond L, 4 * ‖F (ccB b)‖ ^ 2 := Finset.sum_le_sum fun b _ => hpt b
    _ = 4 * ∑ b : Bond L, ‖F (ccB b)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * (8 * coarseEnergy F) := by
        have hs := sum_comp_ccB_le (L := L) (fun c => ‖F c‖ ^ 2) (fun c => sq_nonneg _)
        have : (∑ c : CoarseBond L 2, ‖F c‖ ^ 2) = coarseEnergy F := rfl
        linarith
    _ = 32 * coarseEnergy F := by ring

/-- **The lift is an exact section of `Q` at `U = 1`** (REUSED, not rebuilt:
`FullySupplied.lineCoarseRestrictSuTwo_suTwoLift`, the same section `qCLM_surjective_trivialU`
uses). -/
theorem q_suTwoLift (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (F : CoarseBond L 2 → SuTwo)
    (c : CoarseBond L 2) :
    lineCoarseRestrictCov (trivialU L) 2 (suTwoLift 2 F) c = F c := by
  rw [lineCoarseRestrictCov_trivialU]
  exact lineCoarseRestrictSuTwo_suTwoLift (by norm_num) hdvd F c

#print axioms fibre_card_le
#print axioms sum_comp_ccB_le
#print axioms bondEnergy_suTwoLift_le
#print axioms q_suTwoLift

/-! ## §3 — THE TWO SPLITTINGS, AND THE MASTER INEQUALITY -/

theorem flatCurlValue_sub (A B : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    flatCurlValue (fun b => A b - B b) p = flatCurlValue A p - flatCurlValue B p := by
  simp only [flatCurlValue]
  abel

/-- `‖u−v‖² ≤ 2‖u‖²+2‖v‖²`, summed over plaquettes. -/
theorem curlEnergy_sub_le (A B : Bond L → SuTwo) :
    curlEnergy (fun b => A b - B b) ≤ 2 * curlEnergy A + 2 * curlEnergy B := by
  have hpt : ∀ p : PeriodicLatticePlaquette L,
      ‖flatCurlValue (fun b => A b - B b) p‖ ^ 2
        ≤ 2 * ‖flatCurlValue A p‖ ^ 2 + 2 * ‖flatCurlValue B p‖ ^ 2 := by
    intro p
    rw [flatCurlValue_sub]
    have h := sq_two (flatCurlValue A p) (-flatCurlValue B p)
    rw [norm_neg] at h
    rw [sub_eq_add_neg]
    exact h
  calc curlEnergy (fun b => A b - B b)
      = ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue (fun b => A b - B b) p‖ ^ 2 := rfl
    _ ≤ ∑ p : PeriodicLatticePlaquette L,
          (2 * ‖flatCurlValue A p‖ ^ 2 + 2 * ‖flatCurlValue B p‖ ^ 2) :=
        Finset.sum_le_sum fun p _ => hpt p
    _ = 2 * curlEnergy A + 2 * curlEnergy B := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

/-- `‖A‖² ≤ 2‖A−B‖² + 2‖B‖²`, summed over bonds. -/
theorem bondEnergy_split (A B : Bond L → SuTwo) :
    bondEnergy A ≤ 2 * bondEnergy (fun b => A b - B b) + 2 * bondEnergy B := by
  have hpt : ∀ b : Bond L, ‖A b‖ ^ 2 ≤ 2 * ‖A b - B b‖ ^ 2 + 2 * ‖B b‖ ^ 2 := by
    intro b
    have h := sq_two (A b - B b) (B b)
    rwa [sub_add_cancel] at h
  calc bondEnergy A = ∑ b : Bond L, ‖A b‖ ^ 2 := rfl
    _ ≤ ∑ b : Bond L, (2 * ‖A b - B b‖ ^ 2 + 2 * ‖B b‖ ^ 2) := Finset.sum_le_sum fun b _ => hpt b
    _ = 2 * bondEnergy (fun b => A b - B b) + 2 * bondEnergy B := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

/-- **THE MASTER INEQUALITY — the fibre bound carried to the WHOLE space.**

`bondEnergy A ≤ 13264896 · (curlEnergy A + P_Ax A) + 13583253568 · ‖Q A‖²`

for EVERY `A` on the whole space, at every periodic extent with `2 ∣ (L μ + 1)`. Every constant is
counted:

* `13264896 = 4 · 3316224` — `3316224` is `FibreAggregate`'s own counted `69088 · 48`, and the `4`
  is the two `‖u+v‖² ≤ 2‖u‖²+2‖v‖²` splittings (one on `bondEnergy`, one on `curlEnergy`);
* `13583253568 = 4096 · 3316224 + 64` — `4096 = 2·2·32·32` from those two splittings against
  `curlEnergy(lift) ≤ 32 bondEnergy(lift) ≤ 32·32 ‖QA‖²`, and the `+64 = 2·32` is the lift's own
  share of `bondEnergy`.

NO factor mentions the extent `L`, the volume, or the number of bonds.

This is the SHARP form: the `P_Ax` slot carries only `6632448 = 2 · 3316224`, because §1's
`pAx_sub_suTwoLift` is an EQUALITY and the second `‖u+v‖²` splitting never touches it. The
symmetric `13264896 · (curl + pAx)` form below is a deliberate weakening for the consumer's shape,
and the gap is disclosed rather than hidden inside the numeral. -/
theorem master_defect_bound_sharp (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    bondEnergy A ≤ 13264896 * curlEnergy A + 6632448 * pAx A (CoarseLattice L 2) 2
      + 13583253568 * coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 A) := by
  set F := lineCoarseRestrictCov (trivialU L) 2 A with hF
  set A1 : Bond L → SuTwo := suTwoLift 2 F with hA1
  set A0 : Bond L → SuTwo := fun b => A b - A1 b with hA0
  have hsum : A0 + A1 = A := by
    funext b
    show A b - A1 b + A1 b = A b
    rw [sub_add_cancel]
  have hQ1 : ∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A1 c = F c :=
    fun c => q_suTwoLift hdvd F c
  have hQ0 : ∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A0 c = 0 := by
    intro c
    have h1 : lineCoarseRestrictCov (trivialU L) 2 A c
        = lineCoarseRestrictCov (trivialU L) 2 A0 c
          + lineCoarseRestrictCov (trivialU L) 2 A1 c := by
      rw [← hsum]
      exact lineCoarseRestrictCov_add (trivialU L) 2 A0 A1 c
    rw [hQ1 c, ← hF] at h1
    have h2 : lineCoarseRestrictCov (trivialU L) 2 A0 c + F c = 0 + F c := by
      rw [zero_add]; exact h1.symm
    exact add_right_cancel h2
  have hfib : bondEnergy A0 ≤ 3316224 * (pAx A0 (CoarseLattice L 2) 2 + curlEnergy A0) :=
    aggregate_fibre_bound hdvd A0 hQ0
  have hpax : pAx A0 (CoarseLattice L 2) 2 = pAx A (CoarseLattice L 2) 2 :=
    pAx_sub_suTwoLift A F
  have hcurl0 : curlEnergy A0 ≤ 2 * curlEnergy A + 2 * curlEnergy A1 := curlEnergy_sub_le A A1
  have hcurl1 : curlEnergy A1 ≤ 32 * bondEnergy A1 := plaqEnergy_flatCurl_le A1
  have hbe1 : bondEnergy A1 ≤ 32 * coarseEnergy F := bondEnergy_suTwoLift_le F
  have hsplit : bondEnergy A ≤ 2 * bondEnergy A0 + 2 * bondEnergy A1 := bondEnergy_split A A1
  have hpaxnn : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  rw [hpax] at hfib
  linarith

/-- **THE MASTER INEQUALITY, symmetric form** — the shape §4 and §5 consume. Weaker than
`master_defect_bound_sharp` exactly on the `P_Ax` coefficient (`13264896` in place of `6632448`);
`pAx_nonneg` is what licenses the weakening. -/
theorem master_defect_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    bondEnergy A ≤ 13264896 * (curlEnergy A + pAx A (CoarseLattice L 2) 2)
      + 13583253568 * coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 A) := by
  have h := master_defect_bound_sharp hdvd A
  have hpaxnn : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  linarith

#print axioms flatCurlValue_sub
#print axioms master_defect_bound_sharp
#print axioms curlEnergy_sub_le
#print axioms bondEnergy_split
#print axioms master_defect_bound

/-! ## §4 — THE COERCIVITY FORM, WITH `γ` OUTSIDE THE `∀ L`

`gammaExt a` is a closed-form rational function of the augmentation constant `a` alone. It mentions
no extent, no volume, no bond count, and it is a `def` with a `rfl`-value — there is no data here
for a prover to choose (the `S91` shape audit: the vacuous form would be `∀ L, ∃ γ`, and the
theorem below is `∃ γ, ∀ L`, with the `∃` witness moreover exhibited). -/

/-- `γ_ext(a) = min(1/13264896, a/13583253568)` — explicit, `L`-free. -/
noncomputable def gammaExt (a : ℝ) : ℝ := min (1 / 13264896) (a / 13583253568)

theorem gammaExt_eq (a : ℝ) : gammaExt a = min (1 / 13264896) (a / 13583253568) := rfl

theorem gammaExt_pos {a : ℝ} (ha : 0 < a) : 0 < gammaExt a :=
  lt_min (by norm_num) (by positivity)

/-- At the augmentation `a = 1025` the second branch is inactive and `γ_ext = 1/13264896`
exactly — the constant is a NUMERAL there, not an unevaluated `min`. -/
theorem gammaExt_at_1025 : gammaExt 1025 = 1 / 13264896 := by
  rw [gammaExt_eq, min_eq_left]
  norm_num

/-- **THE EXTENT-UNIFORM WHOLE-SPACE BOUND.** For every augmentation weight `a > 0`, ONE positive
constant `γ_ext a` — chosen before any lattice is named — satisfies

`γ · bondEnergy A ≤ curlEnergy A + P_Ax(A) + a · ‖Q A‖²`

for EVERY periodic extent `L` with `2 ∣ (L μ + 1)` and EVERY whole-space `A`. No fibre hypothesis:
`Q A` is arbitrary. -/
theorem extent_uniform_whole_space {a : ℝ} (ha : 0 < a) (L : PeriodicLatticeExtent)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    gammaExt a * bondEnergy A
      ≤ curlEnergy A + pAx A (CoarseLattice L 2) 2
        + a * coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 A) := by
  set S := curlEnergy A + pAx A (CoarseLattice L 2) 2 with hS
  set E := coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 A) with hE
  have hSnn : (0 : ℝ) ≤ S := by
    have := curlEnergy_nonneg A
    have := pAx_nonneg A (CoarseLattice L 2) 2
    simp only [hS]; linarith
  have hEnn : (0 : ℝ) ≤ E := coarseEnergy_nonneg _
  have hγ0 : (0 : ℝ) ≤ gammaExt a := (gammaExt_pos ha).le
  have hm : bondEnergy A ≤ 13264896 * S + 13583253568 * E := master_defect_bound hdvd A
  have hγK : gammaExt a * 13264896 ≤ 1 := by
    have h := min_le_left (1 / 13264896 : ℝ) (a / 13583253568)
    rw [← gammaExt_eq] at h
    nlinarith
  have hγC : gammaExt a * 13583253568 ≤ a := by
    have h := min_le_right (1 / 13264896 : ℝ) (a / 13583253568)
    rw [← gammaExt_eq] at h
    have : gammaExt a * 13583253568 ≤ (a / 13583253568) * 13583253568 := by nlinarith
    linarith [this, (by ring_nf : (a / 13583253568) * (13583253568 : ℝ) = a)]
  have h1 : gammaExt a * bondEnergy A
      ≤ gammaExt a * (13264896 * S + 13583253568 * E) := mul_le_mul_of_nonneg_left hm hγ0
  have h3 : (gammaExt a * 13264896) * S ≤ 1 * S := mul_le_mul_of_nonneg_right hγK hSnn
  have h4 : (gammaExt a * 13583253568) * E ≤ a * E := mul_le_mul_of_nonneg_right hγC hEnn
  nlinarith

/-- The same statement in the `∃ γ > 0, ∀ L` shape the consumer asked for — the binder order is the
whole point, and it is exhibited here with the witness `gammaExt a` rather than obtained from a
compactness argument (which would give a `γ` INSIDE the `∀ L`). -/
theorem extent_uniform_exists {a : ℝ} (ha : 0 < a) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) →
      ∀ A : Bond L → SuTwo,
        γ * bondEnergy A
          ≤ curlEnergy A + pAx A (CoarseLattice L 2) 2
            + a * coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 A) :=
  ⟨gammaExt a, gammaExt_pos ha, fun L hdvd A => extent_uniform_whole_space ha L hdvd A⟩

#print axioms gammaExt_pos
#print axioms gammaExt_at_1025
#print axioms extent_uniform_whole_space
#print axioms extent_uniform_exists

/-! ## §5 — THE ADAPTER: the same inequality at the tree's own bundled operators

THIN AND SEVERABLE BY DESIGN. §3/§4 above are stated against `curlEnergy`, `pAx`,
`lineCoarseRestrictCov` — the tree's bare forms — so they survive any re-targeting of the rung.
This section only re-expresses them through `deltaKCLMNormalized`, `pAxCLM`, `qCLM`, i.e. in the
literal shape of `TowerOneStep.Rung.gf_of_defect`'s `hdef` argument.

**What this adapter does and does not discharge.** It supplies ONE hypothesis in the
Poincaré-with-defect shape. It does not discharge `hell`, `hdvd`, `hwide`, `hDsym`, `hPsym`,
`hPpos`, `hγ`, `ha`; those remain the consumer's. (`hdvd` at `ell = 2` IS a hypothesis of the
statement below and is therefore visible, not hidden.) -/

/-- The coarse `L²` norm on `CoarseFnL2` is the explicit coarse energy. REUSABLE — the tree had the
bond and plaquette versions (`BondSU2Space.inner_bondFnL2_eq_covBondInner`,
`GeneralUHodge.norm_sq_toLp_plaq`) but not the coarse one. -/
theorem norm_sq_coarseFnL2 (F : CoarseBond L 2 → SuTwo) :
    ‖(WithLp.toLp 2 F : CoarseFnL2 L 2)‖ ^ 2 = coarseEnergy F := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun c _ => real_inner_self_eq_norm_sq (F c)

theorem norm_sq_qCLM (x : BondFnL2 L) :
    ‖qCLM (trivialU L) 2 x‖ ^ 2
      = coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 (WithLp.ofLp x)) := by
  have h : (qCLM (trivialU L) 2 x : CoarseFnL2 L 2)
      = WithLp.toLp 2 (lineCoarseRestrictCov (trivialU L) 2 (WithLp.ofLp x)) := rfl
  rw [h, norm_sq_coarseFnL2]

/-- **THE POINCARÉ-WITH-DEFECT BOUND AT THE TREE'S OWN OPERATORS.**

`γ₀‖x‖² ≤ ⟨x, Δ_k(1) x⟩ + ⟨x, P_Ax x⟩ + C‖Q(1) x‖²`, `γ₀ = 1/13264896`,
`C = 13583253568/13264896`, both `L`-free. This is EXACTLY the shape
`TowerOneStep.Rung.gf_of_defect` consumes (`hC : 0 ≤ C`, `hdef`). -/
theorem defect_bound_at_tree_operators (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (x : BondFnL2 L) :
    (1 / 13264896 : ℝ) * ‖x‖ ^ 2
      ≤ (inner ℝ x (deltaKCLMNormalized (trivialU L) x) : ℝ)
        + (inner ℝ x (pAxCLM (CoarseLattice L 2) 2 x) : ℝ)
        + (13583253568 / 13264896 : ℝ) * ‖qCLM (trivialU L) 2 x‖ ^ 2 := by
  have hx : (WithLp.toLp 2 (WithLp.ofLp x) : BondFnL2 L) = x := rfl
  have hnorm : ‖x‖ ^ 2 = bondEnergy (WithLp.ofLp x) := by
    rw [← hx, norm_sq_bondFnL2]
  have hD : (inner ℝ x (deltaKCLMNormalized (trivialU L) x) : ℝ)
      = curlEnergy (WithLp.ofLp x) := by
    rw [← hx, inner_deltaKCLMNormalized_eq, deltaK_trivialU_eq_curlEnergy]
  have hP : (inner ℝ x (pAxCLM (CoarseLattice L 2) 2 x) : ℝ)
      = pAx (WithLp.ofLp x) (CoarseLattice L 2) 2 := by
    rw [← hx, inner_pAxCLM_eq]
  rw [hnorm, hD, hP, norm_sq_qCLM x]
  have hm := master_defect_bound hdvd (WithLp.ofLp x)
  linarith

#print axioms norm_sq_coarseFnL2
#print axioms norm_sq_qCLM
#print axioms defect_bound_at_tree_operators

/-! ## §6 — THE `‖Qx‖²` TERM IS NOT REMOVABLE: the un-augmented bound is FALSE

This is the loud part. §1 proved the lift is invisible to `P_Ax`. Choose the coarse field supported
on direction `0`: the lift is then also CURL-FREE, because it is constant along every transverse
direction. The result is a nonzero whole-space field annihilated by BOTH `Δ_k(1)` and `P_Ax`, so

    γ‖x‖² ≤ ⟨x, Δ_k(1) x⟩ + ⟨x, P_Ax x⟩

is unsatisfiable for every `γ > 0` AT THESE OPERATORS.

**Scope, stated and not hidden.** `P` here is the tree's own CMP95 `(1.10)` axial form
`pAxCLM (CoarseLattice L 2) 2`. CMP99b `(3.128)`'s gauge-fixing term is `‖RD*·‖²`, a DIFFERENT
object which this tree does not build; nothing below is a statement about that `P`. What is settled
is that the campaign's currently-available `(Δ, P)` pair cannot supply an un-augmented `hDP`, and
therefore that the `a‖Qx‖²` slot of `M = Δ + P + Q*aQ` is load-bearing rather than cosmetic. -/

/-- The coarse mode supported on direction `0`. -/
noncomputable def axisCoarseMode (w : SuTwo) : CoarseBond L 2 → SuTwo :=
  fun c => if c.2 = 0 then w else 0

/-- Its lift: a whole-space fine field living on the ODD layer of direction `0`. -/
noncomputable def liftedAxisField (w : SuTwo) : Bond L → SuTwo :=
  suTwoLift 2 (axisCoarseMode (L := L) w)

theorem liftedAxisField_apply (w : SuTwo) (b : Bond L) :
    liftedAxisField w b =
      if (b.1 b.2).val % 2 = 1 ∧ b.2 = 0 then ((2 : ℕ) : ℝ) • w else 0 := by
  unfold liftedAxisField suTwoLift axisCoarseMode
  by_cases h1 : (b.1 b.2).val % 2 = 2 - 1
  · rw [if_pos h1]
    by_cases h2 : b.2 = 0
    · rw [if_pos h2, if_pos (⟨h1, h2⟩ : (b.1 b.2).val % 2 = 1 ∧ b.2 = 0)]
    · rw [if_neg h2, smul_zero, if_neg (fun hc => h2 hc.2)]
  · rw [if_neg h1, if_neg (fun hc => h1 hc.1)]

theorem liftedAxisField_dir_ne (w : SuTwo) (z : PeriodicLatticeSite L) {ν : Fin 3} (h : ν ≠ 0) :
    liftedAxisField w (z, ν) = 0 := by
  rw [liftedAxisField_apply, if_neg (fun hc => h hc.2)]

theorem liftedAxisField_dir_zero (w : SuTwo) (z : PeriodicLatticeSite L) :
    liftedAxisField w (z, 0) = if (z 0).val % 2 = 1 then ((2 : ℕ) : ℝ) • w else 0 := by
  rw [liftedAxisField_apply]
  by_cases h : (z 0).val % 2 = 1
  · rw [if_pos (⟨h, rfl⟩ : ((z, (0 : Fin 3)).1 (z, (0 : Fin 3)).2).val % 2 = 1
      ∧ (z, (0 : Fin 3)).2 = 0), if_pos h]
  · rw [if_neg (fun hc => h hc.1), if_neg h]

/-- The transverse shift does not move coordinate `0` (`Function.update_of_ne`; the same fact is
`U1Anchor.periodicLatticeShift_apply_ne`, not imported only to keep this module's import surface
at five). -/
theorem shift_coord_zero (z : PeriodicLatticeSite L) {ν : Fin 3} (h : ν ≠ 0) :
    (periodicLatticeShift z ν) 0 = z 0 :=
  Function.update_of_ne (Ne.symm h) _ _

/-- **THE LIFTED AXIS FIELD IS CURL-FREE.** -/
theorem flatCurl_liftedAxisField (w : SuTwo) (p : PeriodicLatticePlaquette L) :
    flatCurlValue (liftedAxisField w) p = 0 := by
  unfold flatCurlValue
  rcases plaq_dirs p.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · rw [liftedAxisField_dir_ne w _ (by decide : (1 : Fin 3) ≠ 0),
      liftedAxisField_dir_ne w _ (by decide : (1 : Fin 3) ≠ 0),
      liftedAxisField_dir_zero, liftedAxisField_dir_zero,
      shift_coord_zero p.1 (by decide : (1 : Fin 3) ≠ 0)]
    abel
  · rw [liftedAxisField_dir_ne w _ (by decide : (2 : Fin 3) ≠ 0),
      liftedAxisField_dir_ne w _ (by decide : (2 : Fin 3) ≠ 0),
      liftedAxisField_dir_zero, liftedAxisField_dir_zero,
      shift_coord_zero p.1 (by decide : (2 : Fin 3) ≠ 0)]
    abel
  · rw [liftedAxisField_dir_ne w _ (by decide : (1 : Fin 3) ≠ 0),
      liftedAxisField_dir_ne w _ (by decide : (2 : Fin 3) ≠ 0),
      liftedAxisField_dir_ne w _ (by decide : (1 : Fin 3) ≠ 0),
      liftedAxisField_dir_ne w _ (by decide : (2 : Fin 3) ≠ 0)]
    abel

theorem curlEnergy_liftedAxisField (w : SuTwo) : curlEnergy (liftedAxisField (L := L) w) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [flatCurl_liftedAxisField w p, norm_zero]
  norm_num

theorem pAx_liftedAxisField (w : SuTwo) :
    pAx (liftedAxisField (L := L) w) (CoarseLattice L 2) 2 = 0 :=
  pAx_suTwoLift (axisCoarseMode w)

/-- A site whose coordinate `0` is ODD exists on every admissible extent. -/
theorem exists_odd_site (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    ∃ z : PeriodicLatticeSite L, (z 0).val = 1 := by
  have h2 : 2 ≤ L 0 + 1 := Nat.le_of_dvd (Nat.succ_pos _) (hdvd 0)
  refine ⟨Function.update (zeroSite L) 0 ⟨1, by omega⟩, ?_⟩
  rw [Function.update_self]

theorem liftedAxisField_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {w : SuTwo}
    (hw : w ≠ 0) : ∃ b : Bond L, liftedAxisField w b ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_odd_site hdvd
  refine ⟨(z, 0), ?_⟩
  rw [liftedAxisField_dir_zero, if_pos (by rw [hz])]
  exact smul_ne_zero (by norm_num) hw

theorem bondEnergy_liftedAxisField_pos (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {w : SuTwo}
    (hw : w ≠ 0) : 0 < bondEnergy (liftedAxisField (L := L) w) := by
  obtain ⟨b, hb⟩ := liftedAxisField_ne_zero hdvd hw
  exact bondEnergy_pos _ hb

/-- **THE REFUTATION.** At the tree's own `Δ_k(1)` and `P_Ax`, the un-augmented gauge-fixed
coercivity is unsatisfiable for EVERY `γ > 0`, at EVERY admissible extent. -/
theorem un_augmented_coercivity_false (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {γ : ℝ}
    (hγ : 0 < γ) :
    ¬ (∀ x : BondFnL2 L, γ * ‖x‖ ^ 2
        ≤ (inner ℝ x (deltaKCLMNormalized (trivialU L) x) : ℝ)
          + (inner ℝ x (pAxCLM (CoarseLattice L 2) 2 x) : ℝ)) := by
  intro hcon
  set A := liftedAxisField (L := L) suTwoWitness with hA
  have h := hcon (WithLp.toLp 2 A)
  rw [norm_sq_bondFnL2, inner_deltaKCLMNormalized_eq, deltaK_trivialU_eq_curlEnergy,
    inner_pAxCLM_eq, curlEnergy_liftedAxisField, pAx_liftedAxisField] at h
  have hpos : 0 < bondEnergy A := bondEnergy_liftedAxisField_pos hdvd suTwoWitness_ne_zero
  nlinarith

/-- **WHAT THAT COSTS THE `gf_of_defect` ROUTE, EXACTLY.** Since the un-augmented bound is false,
the defect bound of §5 can never be converted into a POSITIVE gauge-fixed constant by
`γ₀ − C‖Q‖²`: that number is `≤ 0` at these operators, at every admissible extent. Equivalently
`‖Q(1)‖² ≥ 1/13583253568`. Proved here directly from `qCLM_le` — no import of the rung. -/
theorem gf_of_defect_yields_nothing_here (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    (1 / 13264896 : ℝ) - (13583253568 / 13264896 : ℝ) * ‖qCLM (trivialU L) 2‖ ^ 2 ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  refine un_augmented_coercivity_false hdvd hcon ?_
  intro x
  have hdef := defect_bound_at_tree_operators hdvd x
  have hQ : ‖qCLM (trivialU L) 2 x‖ ≤ ‖qCLM (trivialU L) 2‖ * ‖x‖ :=
    AdalyFormal.Balaban.BridgeInverse.qCLM_le (trivialU L) 2 x
  have hqnn : (0 : ℝ) ≤ ‖qCLM (trivialU L) 2‖ := ContinuousLinearMap.opNorm_nonneg _
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have hsq : ‖qCLM (trivialU L) 2 x‖ ^ 2 ≤ ‖qCLM (trivialU L) 2‖ ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg (qCLM (trivialU L) 2 x)]
  nlinarith

#print axioms liftedAxisField_apply
#print axioms flatCurl_liftedAxisField
#print axioms curlEnergy_liftedAxisField
#print axioms pAx_liftedAxisField
#print axioms un_augmented_coercivity_false
#print axioms gf_of_defect_yields_nothing_here

/-! ## §7 — CONTROLS

Each item answers one way this module could be content-free. -/

section Controls

theorem zeroSite_mem_coarse : zeroSite L ∈ CoarseLattice L 2 :=
  mem_CoarseLattice.2 fun μ => by rw [zeroSite_val]

theorem coarseEnergy_axisCoarseMode_pos {w : SuTwo} (hw : w ≠ 0) :
    0 < coarseEnergy (axisCoarseMode (L := L) w) := by
  have hval : axisCoarseMode (L := L) w (⟨zeroSite L, zeroSite_mem_coarse⟩, 0) = w := if_pos rfl
  have hle : ‖axisCoarseMode (L := L) w (⟨zeroSite L, zeroSite_mem_coarse⟩, 0)‖ ^ 2
      ≤ coarseEnergy (axisCoarseMode (L := L) w) :=
    Finset.single_le_sum (f := fun c : CoarseBond L 2 => ‖axisCoarseMode (L := L) w c‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  rw [hval] at hle
  have : (0 : ℝ) < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  linarith

theorem coarseEnergy_q_liftedAxisField (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) :
    coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 (liftedAxisField w))
      = coarseEnergy (axisCoarseMode (L := L) w) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  show ‖lineCoarseRestrictCov (trivialU L) 2 (suTwoLift 2 (axisCoarseMode w)) c‖ ^ 2
      = ‖axisCoarseMode (L := L) w c‖ ^ 2
  rw [q_suTwoLift hdvd (axisCoarseMode w) c]

/-- **MUST-FIRE, and the term that carries it.** At the lifted axis field the LEFT side is strictly
positive and the RIGHT side is strictly positive too — but `curlEnergy` and `P_Ax` both VANISH
there, so the whole right-hand side is the `a‖QA‖²` term. The inequality is therefore neither
`0 ≤ something` nor a statement the old two terms could have made. -/
theorem master_nonvacuous (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {a : ℝ} (ha : 0 < a) :
    0 < bondEnergy (liftedAxisField (L := L) suTwoWitness)
    ∧ curlEnergy (liftedAxisField (L := L) suTwoWitness) = 0
    ∧ pAx (liftedAxisField (L := L) suTwoWitness) (CoarseLattice L 2) 2 = 0
    ∧ 0 < a * coarseEnergy
        (lineCoarseRestrictCov (trivialU L) 2 (liftedAxisField suTwoWitness))
    ∧ 0 < gammaExt a * bondEnergy (liftedAxisField (L := L) suTwoWitness)
    ∧ gammaExt a * bondEnergy (liftedAxisField (L := L) suTwoWitness)
        ≤ curlEnergy (liftedAxisField (L := L) suTwoWitness)
          + pAx (liftedAxisField (L := L) suTwoWitness) (CoarseLattice L 2) 2
          + a * coarseEnergy
              (lineCoarseRestrictCov (trivialU L) 2 (liftedAxisField suTwoWitness)) := by
  have hbe : 0 < bondEnergy (liftedAxisField (L := L) suTwoWitness) :=
    bondEnergy_liftedAxisField_pos hdvd suTwoWitness_ne_zero
  have hE : 0 < coarseEnergy
      (lineCoarseRestrictCov (trivialU L) 2 (liftedAxisField suTwoWitness)) := by
    rw [coarseEnergy_q_liftedAxisField hdvd]
    exact coarseEnergy_axisCoarseMode_pos suTwoWitness_ne_zero
  refine ⟨hbe, curlEnergy_liftedAxisField _, pAx_liftedAxisField _, by positivity,
    mul_pos (gammaExt_pos ha) hbe, extent_uniform_whole_space ha L hdvd _⟩

/-- **MUST-NOT-FIRE / degenerate point.** At `A = 0` every term is `0`: the bound is an equality
`0 ≤ 0` there, so it is not secretly asserting positivity of something. -/
theorem master_at_zero :
    bondEnergy (fun _ : Bond L => (0 : SuTwo)) = 0
    ∧ curlEnergy (fun _ : Bond L => (0 : SuTwo)) = 0
    ∧ pAx (fun _ : Bond L => (0 : SuTwo)) (CoarseLattice L 2) 2 = 0 := by
  refine ⟨Finset.sum_eq_zero fun b _ => by rw [norm_zero]; norm_num, ?_, ?_⟩
  · refine Finset.sum_eq_zero fun p _ => ?_
    have h : flatCurlValue (fun _ : Bond L => (0 : SuTwo)) p = 0 := by
      unfold flatCurlValue; abel
    rw [h, norm_zero]; norm_num
  · refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x _ => ?_
    have h : pathIntegral (fun _ : Bond L => (0 : SuTwo)) y x = 0 :=
      Finset.sum_eq_zero fun _ _ => rfl
    rw [h, norm_zero]; norm_num

/-- **NO CONSTANT AT ALL WORKS WITHOUT THE `‖QA‖²` TERM.** Not "the constant `13583253568` is
sharp" — the term itself is not removable: for EVERY real `K`, the two-term bound fails. This is
the mutation test on this module's own load-bearing constant, and it fires. -/
theorem no_constant_without_Q_term (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (K : ℝ) :
    ¬ (∀ A : Bond L → SuTwo,
        bondEnergy A ≤ K * (curlEnergy A + pAx A (CoarseLattice L 2) 2)) := by
  intro hcon
  have h := hcon (liftedAxisField (L := L) suTwoWitness)
  rw [curlEnergy_liftedAxisField, pAx_liftedAxisField] at h
  have hbe : 0 < bondEnergy (liftedAxisField (L := L) suTwoWitness) :=
    bondEnergy_liftedAxisField_pos hdvd suTwoWitness_ne_zero
  simp only [add_zero, mul_zero] at h
  linarith

/-- **THE PRICE OF THE DECOMPOSITION, DISCLOSED.** On the fibre `{QA = 0}` this module's constant
is `13264896 = 4 · 3316224`: a factor `4` WEAKER than `FibreAggregate`'s own, from the two
`‖u+v‖² ≤ 2‖u‖² + 2‖v‖²` steps. Both statements are exhibited side by side so the loss is on the
record rather than in a docstring. -/
theorem fibre_case_costs_a_factor_four (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A c = 0) :
    bondEnergy A ≤ 13264896 * (curlEnergy A + pAx A (CoarseLattice L 2) 2)
    ∧ bondEnergy A ≤ 3316224 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A)
    ∧ (13264896 : ℝ) = 4 * 3316224 := by
  have hE : coarseEnergy (lineCoarseRestrictCov (trivialU L) 2 A) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [hQ c, norm_zero]; norm_num
  have hm := master_defect_bound hdvd A
  rw [hE] at hm
  refine ⟨by linarith, aggregate_fibre_bound hdvd A hQ, by norm_num⟩

/-- **`L`-FREENESS, EXHIBITED AT TWO EXTENTS.** The SAME numeral works at the `4³` extent and at
the `6³` extent, on the WHOLE space. `FibreAggregate.card_bond_differs` (reused) proves a
volume-indexed constant could not do this: the bond counts are `192` and `648`. -/
theorem whole_space_two_extents {a : ℝ} (ha : 0 < a) :
    (∀ A : Bond witL3 → SuTwo,
        gammaExt a * bondEnergy A
          ≤ curlEnergy A + pAx A (CoarseLattice witL3 2) 2
            + a * coarseEnergy (lineCoarseRestrictCov (trivialU witL3) 2 A))
    ∧ (∀ A : Bond witL5 → SuTwo,
        gammaExt a * bondEnergy A
          ≤ curlEnergy A + pAx A (CoarseLattice witL5 2) 2
            + a * coarseEnergy (lineCoarseRestrictCov (trivialU witL5) 2 A))
    ∧ Fintype.card (Bond witL3) = 192
    ∧ Fintype.card (Bond witL5) = 648
    ∧ Fintype.card (Bond witL3) ≠ Fintype.card (Bond witL5) :=
  ⟨fun A => extent_uniform_whole_space ha witL3 hdvd_witL3 A,
   fun A => extent_uniform_whole_space ha witL5 hdvd_witL5' A,
   card_bond_witL3, card_bond_witL5, card_bond_differs⟩

/-- **MUST-FIRE AT BOTH EXTENTS.** The witnessing field is nonzero and the bound is non-trivial at
both, so the two-extent statement above is not two vacuous quantifications. -/
theorem must_fire_two_extents :
    0 < bondEnergy (liftedAxisField (L := witL3) suTwoWitness)
    ∧ 0 < bondEnergy (liftedAxisField (L := witL5) suTwoWitness) :=
  ⟨bondEnergy_liftedAxisField_pos hdvd_witL3 suTwoWitness_ne_zero,
   bondEnergy_liftedAxisField_pos hdvd_witL5' suTwoWitness_ne_zero⟩

/-- **THE CONSTANTS, DECOMPOSED IN THE KERNEL** — every factor the header calls "counted" is
asserted here, not only in prose: `32 = ell² · card B(y) = 4 · 8`, `4096 = 2·2·32·32` (the two
`‖u+v‖²` splittings against the two `32`s), `64 = 2·32` (the lift's own share of `bondEnergy`),
and `3316224 = 69088 · 48` is `FibreAggregate`'s own count. -/
theorem constants_are_counted :
    (13264896 : ℝ) = 4 * 3316224
    ∧ (13583253568 : ℝ) = 4096 * 3316224 + 64
    ∧ (3316224 : ℕ) = 69088 * 48
    ∧ (4096 : ℕ) = 2 * 2 * 32 * 32
    ∧ (64 : ℕ) = 2 * 32
    ∧ (32 : ℕ) = 4 * 8 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Both sides are homogeneous of degree `2`, so no rescaling `A ↦ tA` can make the master
inequality true or false. -/
theorem master_is_homogeneous (A : Bond L → SuTwo) (t : ℝ) :
    bondEnergy (fun b => t • A b) = t ^ 2 * bondEnergy A
    ∧ curlEnergy (fun b => t • A b) = t ^ 2 * curlEnergy A := by
  constructor
  · show (∑ b : Bond L, ‖t • A b‖ ^ 2) = t ^ 2 * ∑ b : Bond L, ‖A b‖ ^ 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · show (∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue (fun b => t • A b) p‖ ^ 2)
      = t ^ 2 * ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h : flatCurlValue (fun b => t • A b) p = t • flatCurlValue A p :=
      congrFun (flatCurlValue_smul t A) p
    rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

end Controls

/-! ## §8 — WHAT THE AUGMENTED BOUND ALREADY DISCHARGES AT `M = Δ + P + Q*aQ`

§6 shows the un-augmented bound is unavailable. But `M`'s own diagonal
(`BridgeInverse.fineCLM_inner`, REUSED) is `⟨x,Δx⟩ + ⟨x,Px⟩ + a‖Qx‖²` — precisely the left side of
§5's defect bound. So for `a ≥ C_ext` the WHOLE-SPACE coercivity of `M` holds outright, with an
`L`-free constant and NO coercivity hypothesis anywhere: injectivity of `M` and strict positivity
of its diagonal are theorems here, not assumptions.

These are exactly two of the inputs a first rung needs (`hinj`, `hMpos` in the current `Rung`).
They are NOT the whole rung: `hell`, `hdvd`, `hwide`, `hDsym`, `hPsym`, `hPpos`, `hγ`, `ha` are
separate, and — critically — the tower-law CONSTANT is not supplied by anything below, because that
step consumes the un-augmented form, which §6 refutes at these operators. -/

section MCoercivity

/-- `C_ext = 13583253568/13264896`, the defect constant of §5. -/
noncomputable def cExt : ℝ := 13583253568 / 13264896

theorem cExt_between : 1024 < cExt ∧ cExt < 1025 := by
  constructor <;> · rw [cExt]; norm_num

theorem cExt_pos : 0 < cExt := by rw [cExt]; norm_num

/-- `C_ext` in lowest terms — the numeral the lane's scratchpad elimination reports, asserted in the
kernel rather than left in prose. `gcd(13583253568, 13264896) = 64`. -/
theorem cExt_reduced : cExt = 212238337 / 207264 := by rw [cExt]; norm_num

/-- **`M` IS COERCIVE ON THE WHOLE SPACE**, `L`-free constant `1/13264896`, for every augmentation
weight `a ≥ C_ext`. No coercivity hypothesis is assumed anywhere in the chain behind this. -/
theorem M_coercive_whole_space (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {a : ℝ} (ha : cExt ≤ a)
    (x : BondFnL2 L) :
    (1 / 13264896 : ℝ) * ‖x‖ ^ 2
      ≤ (inner ℝ x (fineCLM (deltaKCLMNormalized (trivialU L))
            (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2)
            (qstarCLM (trivialU L) 2) a x) : ℝ) := by
  rw [fineCLM_inner (deltaKCLMNormalized (trivialU L)) (pAxCLM (CoarseLattice L 2) 2)
    (qCLM (trivialU L) 2) (qstarCLM (trivialU L) 2) a (qCLM_hadj (trivialU L) 2) x]
  have hd := defect_bound_at_tree_operators hdvd x
  have hq : (0 : ℝ) ≤ ‖qCLM (trivialU L) 2 x‖ ^ 2 := sq_nonneg _
  have hmul : cExt * ‖qCLM (trivialU L) 2 x‖ ^ 2 ≤ a * ‖qCLM (trivialU L) 2 x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right ha hq
  rw [cExt] at hmul
  linarith

/-- **`hinj` DISCHARGED** at the tree's own lattice operators, unconditionally for `a ≥ C_ext`. -/
theorem M_injective_whole_space (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {a : ℝ} (ha : cExt ≤ a) :
    Function.Injective (fineCLM (deltaKCLMNormalized (trivialU L))
      (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2) (qstarCLM (trivialU L) 2) a) :=
  injective_of_coercive _ (1 / 13264896) (by norm_num) (M_coercive_whole_space hdvd ha)

/-- **`hMpos` DISCHARGED** at the tree's own lattice operators, unconditionally for `a ≥ C_ext`. -/
theorem M_posdef_whole_space (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {a : ℝ} (ha : cExt ≤ a)
    (x : BondFnL2 L) (hx : x ≠ 0) :
    0 < (inner ℝ x (fineCLM (deltaKCLMNormalized (trivialU L))
      (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2) (qstarCLM (trivialU L) 2) a x) : ℝ) := by
  have h := M_coercive_whole_space hdvd ha x
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have : (0 : ℝ) < (1 / 13264896 : ℝ) * ‖x‖ ^ 2 := by positivity
  linarith

/-- **THE `hMcoerc` SHAPE, WITH THE WEIGHT SHIFTED.** `RecursiveBridge.bridge_coercive_prim` takes
`hMcoerc : ∀ x, γ‖x‖² + a‖Qx‖² ≤ ⟨x, M x⟩` and the SAME `a` reappears in its conclusion. §6 shows
that at these operators such an `hMcoerc` is unavailable when `M`'s own `Q*Q` weight equals that
same `a` — subtracting the two sides would give exactly the un-augmented bound, which is refuted.

It IS available, for every `a₂`, when `M`'s weight is `a₂ + C_ext`:

    (1/13264896)‖x‖² + a₂‖Qx‖² ≤ ⟨x, (Δ_k(1) + P_Ax + (a₂+C_ext)·Q*Q) x⟩

Whether the source permits `M`'s `Q*Q` weight and (3.156)'s subtracted `a` to be different numbers
is a question about (3.16)/(3.156) fidelity; it is NOT settled here and is not this module's to
settle. What is settled is the inequality, with an `L`-free constant. -/
theorem M_coercive_with_slack (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (a2 : ℝ)
    (x : BondFnL2 L) :
    (1 / 13264896 : ℝ) * ‖x‖ ^ 2 + a2 * ‖qCLM (trivialU L) 2 x‖ ^ 2
      ≤ (inner ℝ x (fineCLM (deltaKCLMNormalized (trivialU L))
            (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2)
            (qstarCLM (trivialU L) 2) (a2 + cExt) x) : ℝ) := by
  rw [fineCLM_inner (deltaKCLMNormalized (trivialU L)) (pAxCLM (CoarseLattice L 2) 2)
    (qCLM (trivialU L) 2) (qstarCLM (trivialU L) 2) (a2 + cExt) (qCLM_hadj (trivialU L) 2) x]
  have hd := defect_bound_at_tree_operators hdvd x
  rw [cExt]
  nlinarith [hd]

end MCoercivity

#print axioms M_coercive_with_slack
#print axioms cExt_between
#print axioms M_coercive_whole_space
#print axioms M_injective_whole_space
#print axioms M_posdef_whole_space

#print axioms coarseEnergy_axisCoarseMode_pos
#print axioms master_nonvacuous
#print axioms master_at_zero
#print axioms no_constant_without_Q_term
#print axioms fibre_case_costs_a_factor_four
#print axioms whole_space_two_extents
#print axioms must_fire_two_extents
#print axioms constants_are_counted
#print axioms master_is_homogeneous

/-! ## §9 — FULL AXIOM COVERAGE

The declarations not already printed above, so that EVERY declaration of this module — `def`s
included — has its axiom set on the record, not only the headline theorems. -/

#print axioms pathIntegral_suTwoLift
#print axioms pathIntegral_sub_suTwoLift
#print axioms coarseEnergy
#print axioms coarseEnergy_nonneg
#print axioms ccB
#print axioms gammaExt
#print axioms gammaExt_eq
#print axioms axisCoarseMode
#print axioms liftedAxisField
#print axioms liftedAxisField_dir_ne
#print axioms liftedAxisField_dir_zero
#print axioms shift_coord_zero
#print axioms exists_odd_site
#print axioms liftedAxisField_ne_zero
#print axioms bondEnergy_liftedAxisField_pos
#print axioms zeroSite_mem_coarse
#print axioms coarseEnergy_q_liftedAxisField
#print axioms cExt
#print axioms cExt_pos
#print axioms cExt_reduced

end AdalyFormal.Balaban.ExtentUniformCoercivity
