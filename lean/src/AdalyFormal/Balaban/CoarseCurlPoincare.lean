/-
Copyright (c) 2026 Project Adaly. All rights reserved.
-/
import AdalyFormal.Balaban.RegularUGamma0
import AdalyFormal.Balaban.CoarseCurlCovariant
import AdalyFormal.Balaban.BlockPoincareSharp

/-!
# `[COARSE-CURL-POINCARE]` — the primitive is FALSE AS WRITTEN, and so are the targets above it

**What this module establishes (facts, not verdicts).** `RegularUGamma0` reduces the goal lemma to
two named primitives and states a third open Prop that the general-`U` transfer needs. Three of
those Props quantify their constant OUTSIDE the BLOCK SIZE:

* `RegularUGamma0.CoarseCurlPoincareUniform` — one `γc` for every coarsening factor `m ≥ 2`;
* `RegularUGamma0.Gamma0TrivialUTarget` / `Gamma0UniformTarget` — one `γ₀` for every `m ≥ 2`;
* `RegularUGamma0.KerQDivFreePoincare` — one `K` for every fibre level `ell`.

A lattice field that oscillates on the block scale has curl energy `~ (1/blocksize)²` times its bond
energy, so a constant uniform in the block size cannot exist. This module builds the compiled
witnesses.

## The witnesses

Both are instances of one construction, `coordField μ ν h w`: the su(2) field carried on
direction-`μ` bonds only, with value `h(x ν) • w`, `ν < μ`. §1 computes its bond energy, its flat
curl energy, its coarse average `Q_ell(1)` and its divergence in closed form.

* **W1** (`§4`) — `ell₀ = 1`, torus `L μ + 1 = m = 2p+1` (a single `m`-block), `μ = 2`, `ν = 1`,
  profile `sqProfile p` (`0` at `0`, `+1` on `[1,p]`, `−1` on `[p+1,2p]`). It is in the axial gauge
  (`staircasePath`'s direction-`2` segment sits on the line `x₀ = x₁ = y₁ = 0`, where the profile
  vanishes), it is in `ker Q_m(1)` (`∑ sqProfile p = 0`), and its energy ratio is `2p/6 = p/3 → ∞`.
  It refutes `CoarseCurlPoincareUniform`, `Gamma0TrivialUTarget` and `Gamma0UniformTarget`.
* **W3** (`§6`) — `ell` free, same torus, `μ = 1`, `ν = 0`, same profile. It is divergence-free
  identically (the field direction and the dependence direction differ), it is in `ker Q_ell(1)`,
  and the same ratio refutes `KerQDivFreePoincare`.

## What is NOT claimed

Nothing here says Bałaban's Lemma 2.4 is false, and nothing here touches the `m = 2` content that
`RegularUGamma0` PROVES (`gamma0FibreOneUniform_holds`, `coarseCurlPoincare_fibre_one_trivialU`):
every proved statement there fixes the constraint level at `2`, and W1 needs `m = 2p+1 ≥ 5`. What is
refuted is exactly the free-`m` (respectively free-`ell`) quantification of the three OPEN Props.

**Independent corroboration of the sign of the effect** (different functional, different witness,
different lane): `BlockPoincareSharp.no_subcubic_block_poincare` and
`RegionSummed2123.no_subcubic_region_summed` force any `(2.123)` constant to be `Θ(ell³)`. Those are
lower bounds on a constant that is ALLOWED to depend on the block size; the theorems below are the
non-existence statements for the constants that are NOT.
-/

namespace AdalyFormal.Balaban.CoarseCurlPoincare

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU periodicLatticeShiftBack
  gradCovariantAdjointValue)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict lineIntegralValue)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.RegularUGamma0
open AdalyFormal.Balaban.CoarseCurlCovariant
open AdalyFormal.Balaban.SuTwoGeomU1

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the one-coordinate field `coordField μ ν h w`, and its four closed forms -/

/-- The scalar profile of the witness: the value `h (x ν)` on direction-`μ` bonds, `0` elsewhere. -/
noncomputable def coordScalar (μ ν : Fin 3) (h : Fin (L ν + 1) → ℝ) : Bond L → ℝ :=
  fun b => if b.2 = μ then h (b.1 ν) else 0

/-- **The witness field**: an su(2)-valued bond field carried entirely on direction-`μ` bonds, whose
value depends on the single coordinate `ν`. -/
noncomputable def coordField (μ ν : Fin 3) (h : Fin (L ν + 1) → ℝ) (w : SuTwo) : Bond L → SuTwo :=
  fun b => coordScalar μ ν h b • w

theorem coordField_apply (μ ν : Fin 3) (h : Fin (L ν + 1) → ℝ) (w : SuTwo) (b : Bond L) :
    coordField μ ν h w b = if b.2 = μ then h (b.1 ν) • w else 0 := by
  unfold coordField coordScalar
  by_cases hb : b.2 = μ
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, zero_smul]

/-- Shifting in direction `μ` does not move coordinate `ν ≠ μ`. -/
theorem shift_coord_ne {μ ν : Fin 3} (hne : ν ≠ μ) (x : PeriodicLatticeSite L) :
    (periodicLatticeShift x μ) ν = x ν :=
  Function.update_of_ne hne _ _

/-- …and neither does shifting BACK. -/
theorem shiftBack_coord_ne {μ ν : Fin 3} (hne : ν ≠ μ) (x : PeriodicLatticeSite L) :
    (periodicLatticeShiftBack x μ) ν = x ν :=
  Function.update_of_ne hne _ _

/-- …nor does any iterate (the line-integral path of `Q_ell` runs in direction `μ`). -/
theorem shiftIter_coord_ne {μ ν : Fin 3} (hne : ν ≠ μ) (x : PeriodicLatticeSite L) (j : ℕ) :
    ((fun z => periodicLatticeShift z μ)^[j] x) ν = x ν := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', shift_coord_ne hne, ih]

/-- Shifting in direction `ν` advances coordinate `ν` by one. -/
theorem shift_coord_self (ν : Fin 3) (x : PeriodicLatticeSite L) :
    (periodicLatticeShift x ν) ν = x ν + 1 :=
  Function.update_self _ _ _

/-- **Sum over sites of a function of ONE coordinate** factorizes, with the (positive) cardinality
of the remaining coordinates. Reusable; nothing in it is specific to the witness. -/
theorem sum_site_coord (ν : Fin 3) (F : Fin (L ν + 1) → ℝ) :
    ∑ x : PeriodicLatticeSite L, F (x ν)
      = (Fintype.card ((j : {j : Fin 3 // j ≠ ν}) → Fin (L j.1 + 1)) : ℝ) * ∑ t, F t := by
  classical
  rw [Fintype.sum_equiv (Equiv.piSplitAt ν (fun μ => Fin (L μ + 1)))
    (fun x : PeriodicLatticeSite L => F (x ν))
    (fun q : Fin (L ν + 1) × ((j : {j : Fin 3 // j ≠ ν}) → Fin (L j.1 + 1)) => F q.1)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem card_other_coords_pos (ν : Fin 3) :
    0 < (Fintype.card ((j : {j : Fin 3 // j ≠ ν}) → Fin (L j.1 + 1)) : ℝ) := by
  have h : 0 < Fintype.card ((j : {j : Fin 3 // j ≠ ν}) → Fin (L j.1 + 1)) := Fintype.card_pos
  exact_mod_cast h

/-! ### §1a — bond energy -/

theorem norm_sq_coordField (μ ν : Fin 3) (h : Fin (L ν + 1) → ℝ) (w : SuTwo)
    (x : PeriodicLatticeSite L) (d : Fin 3) :
    ‖coordField μ ν h w (x, d)‖ ^ 2 = if d = μ then h (x ν) ^ 2 * ‖w‖ ^ 2 else 0 := by
  rw [coordField_apply]
  by_cases hb : d = μ
  · rw [if_pos hb, if_pos hb, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · rw [if_neg hb, if_neg hb, norm_zero]
    ring

/-- **The bond energy of the witness field.** -/
theorem bondEnergy_coordField (μ ν : Fin 3) (h : Fin (L ν + 1) → ℝ) (w : SuTwo) :
    bondEnergy (coordField μ ν h w)
      = (∑ x : PeriodicLatticeSite L, h (x ν) ^ 2) * ‖w‖ ^ 2 := by
  classical
  unfold bondEnergy
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : PeriodicLatticeSite L,
      (∑ d : Fin 3, ‖coordField μ ν h w (x, d)‖ ^ 2) = h (x ν) ^ 2 * ‖w‖ ^ 2 := by
    intro x
    rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) => norm_sq_coordField μ ν h w x d),
      Finset.sum_ite_eq' Finset.univ μ (fun _ => h (x ν) ^ 2 * ‖w‖ ^ 2),
      if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hinner x), ← Finset.sum_mul]

/-! ### §1b — the flat curl, and the plaquette energy -/

/-- **The flat curl of the witness field**: nonzero ONLY on the `(ν, μ)` plaquettes, where it is the
one-step difference of the profile. Requires `ν < μ`, which both witnesses satisfy. -/
theorem flatCurl_coordField (μ ν : Fin 3) (hlt : ν < μ) (h : Fin (L ν + 1) → ℝ) (w : SuTwo)
    (p : PeriodicLatticePlaquette L) :
    flatCurlValue (coordField μ ν h w) p
      = if p.2.1.1 = ν ∧ p.2.1.2 = μ then (h (p.1 ν + 1) - h (p.1 ν)) • w else 0 := by
  classical
  obtain ⟨x, ⟨⟨a, b⟩, hab⟩⟩ := p
  show coordField μ ν h w (x, a) + coordField μ ν h w (periodicLatticeShift x a, b)
      - coordField μ ν h w (periodicLatticeShift x b, a) - coordField μ ν h w (x, b) = _
  simp only [coordField_apply]
  by_cases hbμ : b = μ
  · have haμ : a ≠ μ := by
      intro hc
      exact absurd hab (by rw [hc, hbμ]; exact lt_irrefl μ)
    simp only [if_neg haμ, if_pos hbμ]
    by_cases haν : a = ν
    · rw [if_pos (⟨haν, hbμ⟩ : a = ν ∧ b = μ), haν, shift_coord_self, sub_smul]
      abel
    · rw [if_neg (fun hc : a = ν ∧ b = μ => haν hc.1),
        shift_coord_ne (Ne.symm haν : ν ≠ a) x]
      abel
  · by_cases haμ : a = μ
    · have hbν : ν ≠ b := by
        intro hc
        exact absurd hab (by rw [← hc, haμ]; exact not_lt.mpr (le_of_lt hlt))
      simp only [if_pos haμ, if_neg hbμ]
      rw [if_neg (fun hc : a = ν ∧ b = μ => hbμ hc.2), shift_coord_ne hbν x]
      abel
    · simp only [if_neg haμ, if_neg hbμ]
      rw [if_neg (fun hc : a = ν ∧ b = μ => hbμ hc.2)]
      abel

/-- **The plaquette energy of the witness field's curl.** -/
theorem plaqEnergy_coordField (μ ν : Fin 3) (hlt : ν < μ) (h : Fin (L ν + 1) → ℝ) (w : SuTwo) :
    plaqEnergy (flatCurlValue (coordField μ ν h w))
      = (∑ x : PeriodicLatticeSite L, (h (x ν + 1) - h (x ν)) ^ 2) * ‖w‖ ^ 2 := by
  classical
  unfold plaqEnergy
  have hnorm : ∀ (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections),
      ‖flatCurlValue (coordField μ ν h w) (x, d)‖ ^ 2
        = if d = (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)
          then (h (x ν + 1) - h (x ν)) ^ 2 * ‖w‖ ^ 2 else 0 := by
    intro x d
    rw [flatCurl_coordField μ ν hlt h w (x, d)]
    by_cases hc : d = (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)
    · have h1 : ((x, d) : PeriodicLatticePlaquette L).2.1.1 = ν
          ∧ ((x, d) : PeriodicLatticePlaquette L).2.1.2 = μ := by
        rw [show ((x, d) : PeriodicLatticePlaquette L).2 = d from rfl, hc]
        exact ⟨rfl, rfl⟩
      rw [if_pos h1, if_pos hc, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    · have h1 : ¬ (((x, d) : PeriodicLatticePlaquette L).2.1.1 = ν
          ∧ ((x, d) : PeriodicLatticePlaquette L).2.1.2 = μ) := by
        intro hcc
        exact hc (Subtype.ext (Prod.ext hcc.1 hcc.2))
      rw [if_neg h1, if_neg hc, norm_zero]
      ring
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : PeriodicLatticeSite L,
      (∑ d : PeriodicPlaquetteDirections, ‖flatCurlValue (coordField μ ν h w) (x, d)‖ ^ 2)
        = (h (x ν + 1) - h (x ν)) ^ 2 * ‖w‖ ^ 2 := by
    intro x
    rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) => hnorm x d),
      Finset.sum_ite_eq' Finset.univ (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)
        (fun _ => (h (x ν + 1) - h (x ν)) ^ 2 * ‖w‖ ^ 2), if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hinner x), ← Finset.sum_mul]

/-! ### §1c — the coarse average `Q_ell(1)`, and the divergence -/

/-- **`Q_ell(1)` of the witness field**: the block sum of the profile, on direction-`μ` coarse bonds
only. Uses `ν ≠ μ`: the line integral runs in direction `μ` and never moves coordinate `ν`. -/
theorem Q_coordField (ell : ℕ) (μ ν : Fin 3) (hne : ν ≠ μ) (h : Fin (L ν + 1) → ℝ) (w : SuTwo)
    (c : CoarseBond L ell) :
    lineCoarseRestrictCov (trivialU L) ell (coordField μ ν h w) c
      = ((1 / (ell : ℝ) ^ 4)
          * (if c.2 = μ then (ell : ℝ) * ∑ x ∈ blockOf c.1.1 ell, h (x ν) else 0)) • w := by
  classical
  rw [lineCoarseRestrictCov_trivialU]
  have hform : (coordField μ ν h w) = (fun e => (coordScalar μ ν h) e • w) := rfl
  rw [hform, lineCoarseRestrictSuTwo_smul_fixed]
  refine congrArg (fun z : ℝ => z • w) ?_
  unfold lineCoarseRestrict
  refine congrArg (fun z : ℝ => (1 / (ell : ℝ) ^ 4) * z) ?_
  by_cases hc : c.2 = μ
  · rw [if_pos hc]
    have hterm : ∀ x ∈ blockOf c.1.1 ell,
        lineIntegralValue ell (coordScalar μ ν h) x c.2 = (ell : ℝ) * h (x ν) := by
      intro x _
      unfold lineIntegralValue coordScalar
      have hj : ∀ j ∈ Finset.range ell,
          (if (((fun z => periodicLatticeShift z c.2)^[j] x, c.2) : Bond L).2 = μ
            then h ((((fun z => periodicLatticeShift z c.2)^[j] x, c.2) : Bond L).1 ν) else 0)
            = h (x ν) := by
        intro j _
        rw [if_pos hc, hc]
        exact congrArg h (shiftIter_coord_ne hne x j)
      rw [Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold lineIntegralValue coordScalar
    refine Finset.sum_eq_zero fun j _ => ?_
    exact if_neg hc

/-- **The witness field is divergence-free at `U = 1`**, for every profile: the field direction `μ`
and the dependence direction `ν` differ, so the backward shift in direction `μ` does not change the
value. -/
theorem div_coordField (μ ν : Fin 3) (hne : ν ≠ μ) (h : Fin (L ν + 1) → ℝ) (w : SuTwo)
    (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue (trivialU L) (coordField μ ν h w) y = 0 := by
  classical
  unfold gradCovariantAdjointValue
  refine Finset.sum_eq_zero fun d _ => ?_
  have hone : RMap ((trivialU L) (periodicLatticeShiftBack y d, d))⁻¹ = LinearMap.id := by
    show RMap ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))⁻¹ = _
    rw [inv_one, RMap_one]
  rw [hone]
  change coordField μ ν h w (periodicLatticeShiftBack y d, d) - coordField μ ν h w (y, d) = 0
  simp only [coordField_apply]
  by_cases hd : d = μ
  · rw [if_pos hd, if_pos hd]
    change h ((periodicLatticeShiftBack y d) ν) • w - h (y ν) • w = 0
    rw [hd, shiftBack_coord_ne hne y, sub_self]
  · rw [if_neg hd, if_neg hd, sub_self]

/-! ## §2 — the profile: a square wave with a zero at the origin

`sqProfile p` on `Fin (2p+1)`: `0` at `0`, `+1` on `[1,p]`, `−1` on `[p+1,2p]`. Its total sum is
`0` (needed for `ker Q`), it vanishes at `0` (needed for the axial gauge), its square sums to `2p`,
and its one-step difference is supported on the three points `0`, `p`, `2p` with squares
`1 + 4 + 1 = 6`. Three jumps is optimal: a profile with `h 0 = 0` and `∑ h = 0` and only two jumps
is identically `0`. -/

/-- The profile, as a function of the raw index. -/
noncomputable def sqN (p : ℕ) (k : ℕ) : ℝ := if k = 0 then 0 else if k ≤ p then 1 else -1

/-- The profile on the periodic coordinate. -/
noncomputable def sqProfile (p : ℕ) (t : Fin (2 * p + 1)) : ℝ := sqN p t.val

theorem sqProfile_zero (p : ℕ) : sqProfile p (0 : Fin (2 * p + 1)) = 0 := by
  unfold sqProfile sqN
  rw [show ((0 : Fin (2 * p + 1))).val = 0 from rfl, if_pos rfl]

theorem sum_sqN (p : ℕ) : ∑ k ∈ Finset.range (2 * p + 1), sqN p k = 0 := by
  rw [Finset.range_eq_Ico]
  have e1 : ∑ k ∈ Finset.Ico 0 1, sqN p k + ∑ k ∈ Finset.Ico 1 (2 * p + 1), sqN p k
      = ∑ k ∈ Finset.Ico 0 (2 * p + 1), sqN p k :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have e2 : ∑ k ∈ Finset.Ico 1 (p + 1), sqN p k + ∑ k ∈ Finset.Ico (p + 1) (2 * p + 1), sqN p k
      = ∑ k ∈ Finset.Ico 1 (2 * p + 1), sqN p k :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have a1 : ∑ k ∈ Finset.Ico 0 1, sqN p k = 0 := by
    rw [show Finset.Ico 0 1 = ({0} : Finset ℕ) by decide, Finset.sum_singleton]
    unfold sqN; rw [if_pos rfl]
  have a2 : ∑ k ∈ Finset.Ico 1 (p + 1), sqN p k = (p : ℝ) := by
    have hc : ∀ k ∈ Finset.Ico 1 (p + 1), sqN p k = 1 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      unfold sqN
      rw [if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
      show p + 1 - 1 = p by omega]
    simp
  have a3 : ∑ k ∈ Finset.Ico (p + 1) (2 * p + 1), sqN p k = -(p : ℝ) := by
    have hc : ∀ k ∈ Finset.Ico (p + 1) (2 * p + 1), sqN p k = -1 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      unfold sqN
      rw [if_neg (by omega), if_neg (by omega)]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
      show 2 * p + 1 - (p + 1) = p by omega]
    simp
  linarith [e1, e2, a1, a2, a3]

theorem sum_sqN_sq (p : ℕ) : ∑ k ∈ Finset.range (2 * p + 1), (sqN p k) ^ 2 = 2 * (p : ℝ) := by
  rw [Finset.range_eq_Ico]
  have e1 : ∑ k ∈ Finset.Ico 0 1, (sqN p k) ^ 2 + ∑ k ∈ Finset.Ico 1 (2 * p + 1), (sqN p k) ^ 2
      = ∑ k ∈ Finset.Ico 0 (2 * p + 1), (sqN p k) ^ 2 :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have e2 : ∑ k ∈ Finset.Ico 1 (p + 1), (sqN p k) ^ 2
        + ∑ k ∈ Finset.Ico (p + 1) (2 * p + 1), (sqN p k) ^ 2
      = ∑ k ∈ Finset.Ico 1 (2 * p + 1), (sqN p k) ^ 2 :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have a1 : ∑ k ∈ Finset.Ico 0 1, (sqN p k) ^ 2 = 0 := by
    rw [show Finset.Ico 0 1 = ({0} : Finset ℕ) by decide, Finset.sum_singleton]
    unfold sqN; rw [if_pos rfl]; norm_num
  have a2 : ∑ k ∈ Finset.Ico 1 (p + 1), (sqN p k) ^ 2 = (p : ℝ) := by
    have hc : ∀ k ∈ Finset.Ico 1 (p + 1), (sqN p k) ^ 2 = 1 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      unfold sqN
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
      show p + 1 - 1 = p by omega]
    simp
  have a3 : ∑ k ∈ Finset.Ico (p + 1) (2 * p + 1), (sqN p k) ^ 2 = (p : ℝ) := by
    have hc : ∀ k ∈ Finset.Ico (p + 1) (2 * p + 1), (sqN p k) ^ 2 = 1 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      unfold sqN
      rw [if_neg (by omega), if_neg (by omega)]; norm_num
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
      show 2 * p + 1 - (p + 1) = p by omega]
    simp
  linarith [e1, e2, a1, a2, a3]

theorem sum_sqProfile (p : ℕ) : ∑ t : Fin (2 * p + 1), sqProfile p t = 0 := by
  rw [show (fun t : Fin (2 * p + 1) => sqProfile p t) = (fun t : Fin (2 * p + 1) => sqN p t.val)
    from rfl]
  rw [Fin.sum_univ_eq_sum_range (fun k => sqN p k) (2 * p + 1)]
  exact sum_sqN p

theorem sum_sqProfile_sq (p : ℕ) : ∑ t : Fin (2 * p + 1), (sqProfile p t) ^ 2 = 2 * (p : ℝ) := by
  rw [show (fun t : Fin (2 * p + 1) => (sqProfile p t) ^ 2)
    = (fun t : Fin (2 * p + 1) => (sqN p t.val) ^ 2) from rfl]
  rw [Fin.sum_univ_eq_sum_range (fun k => (sqN p k) ^ 2) (2 * p + 1)]
  exact sum_sqN_sq p

/-- The three jump sites of the profile. -/
def zeroIdx (p : ℕ) : Fin (2 * p + 1) := ⟨0, by omega⟩
def pIdx (p : ℕ) : Fin (2 * p + 1) := ⟨p, by omega⟩
def p2Idx (p : ℕ) : Fin (2 * p + 1) := ⟨2 * p, by omega⟩

theorem zeroIdx_val (p : ℕ) : (zeroIdx p).val = 0 := rfl
theorem pIdx_val (p : ℕ) : (pIdx p).val = p := rfl
theorem p2Idx_val (p : ℕ) : (p2Idx p).val = 2 * p := rfl

/-- **The one-step difference of the profile is supported on exactly three sites**, with squares
`1`, `4`, `1`. -/
theorem sqProfile_diff_sq (p : ℕ) (hp : 1 ≤ p) (t : Fin (2 * p + 1)) :
    (sqProfile p (t + 1) - sqProfile p t) ^ 2
      = (if t = zeroIdx p then (1 : ℝ) else 0) + (if t = pIdx p then (4 : ℝ) else 0)
        + (if t = p2Idx p then (1 : ℝ) else 0) := by
  classical
  have hz : (t = zeroIdx p) ↔ t.val = 0 := by rw [Fin.ext_iff, zeroIdx_val]
  have hpi : (t = pIdx p) ↔ t.val = p := by rw [Fin.ext_iff, pIdx_val]
  have hp2 : (t = p2Idx p) ↔ t.val = 2 * p := by rw [Fin.ext_iff, p2Idx_val]
  have hub : t.val < 2 * p + 1 := t.isLt
  by_cases htl : t = Fin.last (2 * p)
  · have hv : t.val = 2 * p := by rw [htl, Fin.val_last]
    have h1 : ((t + 1) : Fin (2 * p + 1)).val = 0 := by rw [Fin.val_add_one, if_pos htl]
    rw [if_neg (fun hc => by have := hz.mp hc; omega),
      if_neg (fun hc => by have := hpi.mp hc; omega), if_pos (hp2.mpr hv)]
    unfold sqProfile sqN
    rw [h1, hv, if_pos rfl, if_neg (by omega), if_neg (by omega)]
    norm_num
  · have hne : t.val ≠ 2 * p := fun hc => htl (Fin.ext (by rw [hc, Fin.val_last]))
    have h1 : ((t + 1) : Fin (2 * p + 1)).val = t.val + 1 := by
      rw [Fin.val_add_one, if_neg htl]
    rw [if_neg (fun hc => hne (hp2.mp hc))]
    rcases Nat.lt_or_ge t.val p with hlt | hge
    · rcases Nat.eq_zero_or_pos t.val with h0 | hpos
      · rw [if_pos (hz.mpr h0), if_neg (fun hc => by have := hpi.mp hc; omega)]
        unfold sqProfile sqN
        rw [h1, h0, if_pos rfl, if_neg (by omega), if_pos (by omega)]
        norm_num
      · rw [if_neg (fun hc => by have := hz.mp hc; omega),
          if_neg (fun hc => by have := hpi.mp hc; omega)]
        unfold sqProfile sqN
        rw [h1, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        norm_num
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · rw [if_neg (fun hc => by have := hz.mp hc; omega), if_pos (hpi.mpr heq.symm)]
        unfold sqProfile sqN
        rw [h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        norm_num
      · rw [if_neg (fun hc => by have := hz.mp hc; omega),
          if_neg (fun hc => by have := hpi.mp hc; omega)]
        unfold sqProfile sqN
        rw [h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        norm_num

theorem sum_sqProfile_diff (p : ℕ) (hp : 1 ≤ p) :
    ∑ t : Fin (2 * p + 1), (sqProfile p (t + 1) - sqProfile p t) ^ 2 = 6 := by
  classical
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => sqProfile_diff_sq p hp t)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (zeroIdx p) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (pIdx p) (fun _ => (4 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (p2Idx p) (fun _ => (1 : ℝ))]
  rw [if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  norm_num


/-! ## §3 — the witness torus: ONE block of side `2p+1`, and the witness field on it -/

/-- The witness extent: `L μ + 1 = 2p+1` in every direction, so the whole torus is a SINGLE block
at level `2p+1`. (`4 ≤ L μ` holds as soon as `2 ≤ p`.) -/
def witExt (p : ℕ) : PeriodicLatticeExtent := fun _ => 2 * p

theorem witExt_apply (p : ℕ) (μ : Fin 3) : witExt p μ = 2 * p := rfl

/-- The profile at the type the lattice hands us (`Fin (witExt p ν + 1) = Fin (2p+1)`), so that no
lemma below has to unify a lattice extent with a numeral. -/
noncomputable def witProfile (p : ℕ) (ν : Fin 3) : Fin (witExt p ν + 1) → ℝ := fun t => sqN p t.val

theorem witProfile_zero (p : ℕ) (ν : Fin 3) :
    witProfile p ν (0 : Fin (witExt p ν + 1)) = 0 := sqProfile_zero p

theorem sum_witProfile (p : ℕ) (ν : Fin 3) : ∑ t, witProfile p ν t = 0 := sum_sqProfile p

theorem sum_witProfile_sq (p : ℕ) (ν : Fin 3) :
    ∑ t, (witProfile p ν t) ^ 2 = 2 * (p : ℝ) := sum_sqProfile_sq p

theorem sum_witProfile_diff (p : ℕ) (hp : 1 ≤ p) (ν : Fin 3) :
    ∑ t, (witProfile p ν (t + 1) - witProfile p ν t) ^ 2 = 6 := sum_sqProfile_diff p hp

/-- **At level `2p+1` the only coarse site is the origin** (the torus is one block). -/
theorem coarse_site_zero (p : ℕ) {y : PeriodicLatticeSite (witExt p)}
    (hy : y ∈ CoarseLattice (witExt p) (2 * p + 1)) (μ : Fin 3) : (y μ).val = 0 := by
  have h : (y μ).val % (2 * p + 1) = 0 := mem_CoarseLattice.mp hy μ
  have hlt : (y μ).val < 2 * p + 1 := (y μ).isLt
  rwa [Nat.mod_eq_of_lt hlt] at h

/-- **…so the block at any coarse site is the whole torus.** -/
theorem block_univ (p : ℕ) {y : PeriodicLatticeSite (witExt p)}
    (hy : y ∈ CoarseLattice (witExt p) (2 * p + 1)) :
    blockOf y (2 * p + 1) = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => ?_
  rw [mem_blockOf]
  intro μ
  have h0 := coarse_site_zero p hy μ
  have hlt : (x μ).val < 2 * p + 1 := (x μ).isLt
  omega

/-- **The witness is in `ker Q_{2p+1}(1)`** — for EVERY placement `(μ, ν)` with `ν ≠ μ`, because the
profile sums to zero over the (single) block. -/
theorem witness_kerQ (p : ℕ) (μ ν : Fin 3) (hne : ν ≠ μ) (w : SuTwo)
    (c : CoarseBond (witExt p) (2 * p + 1)) :
    lineCoarseRestrictCov (trivialU (witExt p)) (2 * p + 1)
      (coordField μ ν (witProfile p ν) w) c = 0 := by
  classical
  rw [Q_coordField (2 * p + 1) μ ν hne (witProfile p ν) w c]
  have hsum : ∑ x ∈ blockOf c.1.1 (2 * p + 1), witProfile p ν (x ν) = 0 := by
    rw [block_univ p c.1.2]
    rw [show (∑ x ∈ (Finset.univ : Finset (PeriodicLatticeSite (witExt p))),
          witProfile p ν (x ν))
        = ∑ x : PeriodicLatticeSite (witExt p), witProfile p ν (x ν) from rfl,
      sum_site_coord ν (witProfile p ν), sum_witProfile p ν, mul_zero]
  by_cases hc : c.2 = μ
  · rw [if_pos hc, hsum, mul_zero, mul_zero, zero_smul]
  · rw [if_neg hc, mul_zero, zero_smul]

/-- **The exact energy relation of the witness**: `bondEnergy · 6 = plaqEnergy · 2p`. Division-free,
so the block-size degradation is visible with no estimate anywhere. -/
theorem witness_energies (p : ℕ) (hp : 1 ≤ p) (μ ν : Fin 3) (hlt : ν < μ) (w : SuTwo) :
    bondEnergy (coordField (L := witExt p) μ ν (witProfile p ν) w) * 6
      = plaqEnergy (flatCurlValue (coordField (L := witExt p) μ ν (witProfile p ν) w))
        * (2 * (p : ℝ)) := by
  rw [bondEnergy_coordField, plaqEnergy_coordField μ ν hlt,
    sum_site_coord ν (fun t => (witProfile p ν t) ^ 2),
    sum_site_coord ν (fun t => (witProfile p ν (t + 1) - witProfile p ν t) ^ 2),
    sum_witProfile_sq p ν, sum_witProfile_diff p hp ν]
  ring

/-- The witness has strictly positive curl energy (so nothing below divides by zero). -/
theorem witness_plaq_pos (p : ℕ) (hp : 1 ≤ p) (μ ν : Fin 3) (hlt : ν < μ) {w : SuTwo}
    (hw : w ≠ 0) :
    0 < plaqEnergy (flatCurlValue (coordField (L := witExt p) μ ν (witProfile p ν) w)) := by
  rw [plaqEnergy_coordField μ ν hlt,
    sum_site_coord ν (fun t => (witProfile p ν (t + 1) - witProfile p ν t) ^ 2),
    sum_witProfile_diff p hp ν]
  have hC := card_other_coords_pos (L := witExt p) ν
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  positivity

/-! ## §4 — W1: the axial-gauge witness at `ell₀ = 1`, and the three refutations -/

/-- **W1**: the field `sqProfile p (x₁) • w` on direction-`2` bonds. -/
noncomputable def W1 (p : ℕ) (w : SuTwo) : Bond (witExt p) → SuTwo :=
  coordField 2 1 (witProfile p 1) w

/-- **W1 is in the axial gauge at level `2p+1`.** `staircasePath`'s direction-`2` segment is pinned
to the line `x₀ = y₀`, `x₁ = y₁` (`AdmissibleSubspace.axisSegment`), the only coarse site is the
origin, and the profile vanishes at `0`. The direction-`0` and direction-`1` segments carry no field
at all. -/
theorem W1_axial (p : ℕ) (w : SuTwo) {y : PeriodicLatticeSite (witExt p)}
    (hy : y ∈ CoarseLattice (witExt p) (2 * p + 1)) (x : PeriodicLatticeSite (witExt p))
    (b : Bond (witExt p)) (hb : b ∈ staircasePath y x) : W1 p w b = 0 := by
  classical
  unfold W1
  rw [coordField_apply]
  by_cases hd : b.2 = 2
  · rw [if_pos hd]
    rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
    rcases hb with (hb | hb) | hb
    · rw [mem_axisSegment] at hb
      have h1 : b.1 1 = y 1 := hb.2.1 1 (by decide)
      have hy1 : y 1 = (0 : Fin (witExt p 1 + 1)) := Fin.ext (coarse_site_zero p hy 1)
      rw [h1, hy1, witProfile_zero, zero_smul]
    · rw [mem_axisSegment] at hb
      exact absurd (hb.1.symm.trans hd) (by decide)
    · rw [mem_axisSegment] at hb
      exact absurd (hb.1.symm.trans hd) (by decide)
  · rw [if_neg hd]

/-- **W1 is in `ker Q_{2p+1}(1)`.** -/
theorem W1_kerQ (p : ℕ) (w : SuTwo) (c : CoarseBond (witExt p) (2 * p + 1)) :
    lineCoarseRestrictCov (trivialU (witExt p)) (2 * p + 1) (W1 p w) c = 0 :=
  witness_kerQ p 2 1 (by decide) w c

/-- At `U = 1` the covariant curl IS the flat curl (used to read the goal's right-hand side). -/
theorem curl_trivialU_eq_flat (A : Bond L → SuTwo) :
    curlCovariantLM (trivialU L) A = flatCurlValue A := by
  rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl

/-- **The arithmetic core of the refutation, isolated so every statement below uses ONE copy**
(LAW-19): any constant `γ` for which W1 satisfies `γ · bondEnergy ≤ plaqEnergy(∂B)` obeys
`γ · 2p ≤ 6`. Division-free; the only inputs are the exact energy relation and the strict positivity
of the curl energy. -/
theorem witness_forces_bound {γ : ℝ} (p : ℕ) (hp : 1 ≤ p) {w : SuTwo} (hw : w ≠ 0)
    (h : γ * bondEnergy (W1 p w) ≤ plaqEnergy (flatCurlValue (W1 p w))) :
    γ * (2 * (p : ℝ)) ≤ 6 := by
  have hrel := witness_energies p hp 2 1 (by decide) w
  have hpos := witness_plaq_pos p hp 2 1 (by decide) hw
  rw [show W1 p w = coordField (L := witExt p) 2 1 (witProfile p 1) w from rfl] at h
  set b := bondEnergy (coordField (L := witExt p) 2 1 (witProfile p 1) w) with hbdef
  set q := plaqEnergy (flatCurlValue (coordField (L := witExt p) 2 1 (witProfile p 1) w)) with hqdef
  have hq2p : (2 * (p : ℝ)) * q = 6 * b := by linarith [hrel]
  have key : (γ * (2 * (p : ℝ))) * q ≤ 6 * q := by
    calc (γ * (2 * (p : ℝ))) * q = γ * ((2 * (p : ℝ)) * q) := by ring
      _ = γ * (6 * b) := by rw [hq2p]
      _ = 6 * (γ * b) := by ring
      _ ≤ 6 * q := by linarith [h]
  exact le_of_mul_le_mul_right key hpos

/-- **`[COARSE-CURL-POINCARE]` IS FALSE AS WRITTEN.** No `γc > 0` works for every coarsening factor
`m`: at `ell₀ = 1`, `m = 2p+1`, W1 forces `γc · 2p ≤ 6`. -/
theorem not_coarseCurlPoincareUniform : ¬ CoarseCurlPoincareUniform := by
  classical
  rintro ⟨γc, hγc, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / γc)
  set p := max 2 n with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hpn : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_max_right 2 n
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hkey := hall (witExt p) 1 (2 * p + 1) one_pos (by omega)
    (fun _ => by show 4 ≤ 2 * p; omega) (fun _ => one_dvd _)
    (fun _ => by rw [one_mul]; exact dvd_refl _) (trivialU _) (W1 p suTwoWitness)
    (by rw [one_mul]; exact fun y hy x _ b hb => W1_axial p suTwoWitness hy x b hb)
    (by rw [one_mul]; exact fun c => W1_kerQ p suTwoWitness c)
  rw [covCoarseBondInner_one_eq_bondEnergy, coarseCurlEnergySuTwo_one_eq_plaqEnergy,
    curl_trivialU_eq_flat] at hkey
  have hb := witness_forces_bound p (by omega) hw hkey
  have hgt : 3 < γc * (p : ℝ) := by
    rw [div_lt_iff₀ hγc] at hn
    nlinarith [hn, hpn, hγc]
  nlinarith [hb, hgt]

/-- **`Gamma0TrivialUTarget` IS FALSE AS WRITTEN** — same witness, read against the actual Schur
complement, which at `ell₀ = 1` IS the raw curl form
(`CovariantHjFaithful.deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm`). So the defect is in the
TARGET, not only in the primitive that was offered as sufficient for it. -/
theorem not_gamma0TrivialUTarget : ¬ Gamma0TrivialUTarget := by
  classical
  rintro ⟨γ₀, hγ₀, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / γ₀)
  set p := max 2 n with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hpn : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_max_right 2 n
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hkey := hall (witExt p) 1 (2 * p + 1) one_pos (by omega)
    (fun _ => by show 4 ≤ 2 * p; omega) (fun _ => one_dvd _)
    (fun _ => by rw [one_mul]; exact dvd_refl _) ([] : List (KernelSubspace.Level (witExt p)))
    (W1 p suTwoWitness)
    (by rw [one_mul]; exact fun y hy x _ b hb => W1_axial p suTwoWitness hy x b hb)
    (by rw [one_mul]; exact fun c => W1_kerQ p suTwoWitness c)
  rw [covCoarseBondInner_one_eq_bondEnergy, deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm] at hkey
  have hd : CovariantHj.dstarDQuadForm (trivialU (witExt p)) (W1 p suTwoWitness)
      = plaqEnergy (flatCurlValue (W1 p suTwoWitness)) := by
    show covPlaqInner (curlCovariantLM (trivialU (witExt p)) (W1 p suTwoWitness))
      (curlCovariantLM (trivialU (witExt p)) (W1 p suTwoWitness)) = _
    rw [curl_trivialU_eq_flat, covPlaqInner_self_eq_plaqEnergy]
  rw [hd] at hkey
  have hb := witness_forces_bound p (by omega) hw hkey
  have hgt : 3 < γ₀ * (p : ℝ) := by
    rw [div_lt_iff₀ hγ₀] at hn
    nlinarith [hn, hpn, hγ₀]
  nlinarith [hb, hgt]

/-- **`Gamma0UniformTarget` IS FALSE AS WRITTEN** — it implies the `U = 1` target, since
`frobSupBond (trivialU) = 0 ≤ α₀`. -/
theorem not_gamma0UniformTarget : ¬ Gamma0UniformTarget := by
  classical
  rintro ⟨γ₀, α₀, hγ₀, hα₀, hall⟩
  refine not_gamma0TrivialUTarget ⟨γ₀, hγ₀, ?_⟩
  intro L ell₀ m hell₀ hm hL hdvd₀ hdvdm levels _ _ B hadm hker
  exact hall L ell₀ m hell₀ hm hL hdvd₀ hdvdm (trivialU L)
    (by rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]; exact le_of_lt hα₀)
    levels B hadm hker

/-! ## §5 — W3: the divergence-free witness, and `[KERQ-DIVFREE-POINCARE]` -/

/-- **W3**: the field `sqProfile p (x₀) • w` on direction-`1` bonds. -/
noncomputable def W3 (p : ℕ) (w : SuTwo) : Bond (witExt p) → SuTwo :=
  coordField 1 0 (witProfile p 0) w

theorem W3_kerQ (p : ℕ) (w : SuTwo) (c : CoarseBond (witExt p) (2 * p + 1)) :
    lineCoarseRestrictCov (trivialU (witExt p)) (2 * p + 1) (W3 p w) c = 0 :=
  witness_kerQ p 1 0 (by decide) w c

theorem W3_divFree (p : ℕ) (w : SuTwo) (y : PeriodicLatticeSite (witExt p)) :
    gradCovariantAdjointValue (trivialU (witExt p)) (W3 p w) y = 0 :=
  div_coordField 1 0 (by decide) (witProfile p 0) w y

/-- **`[KERQ-DIVFREE-POINCARE]` IS FALSE AS WRITTEN.** `RegularUGamma0`'s §11a control showed that
the `chiField` witness does NOT refute the divergence-free form; this one does, by a different
mechanism. `chiField` is curl-FREE and would refute any constant at a fixed level; W3 has nonzero
curl and refutes only the UNIFORMITY in `ell` — the reverse Poincaré on
`ker Q_ell(1) ∩ {∂* = 0}` forces `2p ≤ 6K` at level `ell = 2p+1`, so `K` must grow at least linearly
in the fibre level. -/
theorem not_kerQDivFreePoincare : ¬ KerQDivFreePoincare := by
  classical
  rintro ⟨K, hK, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * K)
  set p := max 2 n with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hpn : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_max_right 2 n
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hkey := hall (witExt p) (2 * p + 1) (by omega) (fun _ => dvd_refl _)
    (W3 p suTwoWitness) (fun c => W3_kerQ p suTwoWitness c) (fun y => W3_divFree p suTwoWitness y)
  rw [curl_trivialU_eq_flat] at hkey
  have hrel := witness_energies p (by omega) 1 0 (by decide) (suTwoWitness : SuTwo)
  have hpos := witness_plaq_pos p (by omega) 1 0 (by decide) hw
  have hgt : 3 * K < (p : ℝ) := lt_of_lt_of_le hn hpn
  rw [show W3 p (suTwoWitness : SuTwo)
      = coordField (L := witExt p) 1 0 (witProfile p 0) suTwoWitness from rfl] at hkey
  nlinarith [hkey, hrel, hpos, hgt, hK]

/-! ## §6 — THE SCALE-CORRECTED SUCCESSOR, and whether the reduction survives

The refutations of §4/§5 all attack ONE quantifier: a constant demanded uniformly over the block
size. Bałaban's own statement carries a scale factor, and in the RG the coarsening ratio `m` is
FIXED (it is the RG scale factor `L₀`; the running index is `ell₀ = L₀^k`). So the honest successor
demands uniformity in `L`, `ell₀`, `U`, `B` — i.e. in `k` — at each FIXED `m`. Two forms are stated
below, and BOTH primitives are now written over the COVARIANT coarse curl of `CoarseCurlCovariant`
(at `U = 1` that IS `coarseCurlSuTwo`, `coarseCurlEnergyCov_trivialU`, so the `U = 1` content of
`RegularUGamma0` transfers unchanged, and the pure-gauge witness that refutes the flat
`SummedTransferRegularU` does not touch the covariant one).

* `CoarseCurlPoincareAtScale m` — `m` fixed, `γc` outside `L`, `ell₀`, `U`, `B`. This is the
  successor primitive.
* `CoarseCurlPoincareScaled r` — the quantitative form: one `γc` for all `m`, with the constant
  allowed to decay as `m^{-r}`. `r = 0` is the refuted original. `scaled_imp_atScale` shows the
  scaled form implies the fixed-scale form at every `m`, so `r` is exactly the "how fast may the
  constant decay" parameter, and the refutations below are lower bounds on `r`.

**The reduction SURVIVES** (`gamma0AtScale_of_two_primitives`): `[SUMMED-TRANSFER-U-COV]` +
`CoarseCurlPoincareAtScale m` ⟹ the goal lemma at that `m`, with `γ₀ = cT · γc`. Nothing in
`RegularUGamma0.gamma0UniformTarget_of_two_primitives`'s argument used the `m`-uniformity; it is
reproduced here over the covariant coarse curl.

**SUPERSEDED IN PART (2026-07-27), retained above verbatim — read this before using §6.**
`CoarseCurlScaleTwo` proves `¬ CoarseCurlPoincareAtScale m` for EVERY `m ≥ 2` and
`¬ CoarseCurlPoincareScaled r` for EVERY `r`. The statements below are unchanged and every theorem
below is unchanged and still true; what changed is their standing:

* `gamma0AtScale_of_two_primitives` remains a valid IMPLICATION, but its second antecedent is now
  known false, so it no longer delivers the goal lemma — the reduction is not a general route.
* `scaled_imp_atScale` is unaffected (it is now used contrapositively).
* `coarseCurlPoincareAtScale_instance_one_two` is unaffected: individual instances of the
  primitive's body are provable; what fails is the universal quantification over `ell₀ ≥ 2`.
* `not_coarseCurlPoincareScaled_zero` (`r = 0`) is strictly weaker than
  `CoarseCurlScaleTwo.not_coarseCurlPoincareScaled` and is kept as the independent `ell₀ = 1`
  witness (a different mechanism: oscillation on the block scale, not gauge non-descent).
* the exponent bracket `1 ≤ r ≤ 5` recorded for `CoarseCurlPoincareScaled` does NOT close: no `r`
  works. The bracket remains meaningful only for the `ell₀ = 1` FIBRE, which §7 proves at `r = 5`
  and which `CoarseCurlScaleTwo.not_coarseCurlPoincareFibreOne_one` (a periodic sawtooth) refutes
  at `r = 1` — so the fibre's compiled bracket is `2 ≤ r ≤ 5`. Note `witness_satisfies_scaled_two`
  below: §4's square wave SATISFIES the `r = 2` form, so it could never have forced `r ≥ 2`; a
  profile with amplitude `Θ(m)` built from `Θ(m)` unit steps is required.

The mechanism of the new refutation is disjoint from §4's: it is not about the constant's scale
dependence at all, but about the axial gauge failing to descend from the fine lattice to the coarse
one, so that `Q_{ell₀}B` can be a nonzero coarse-curl-free coarse field. -/

/-- **THE SUCCESSOR PRIMITIVE `[COARSE-CURL-POINCARE-AT-SCALE m]`** — `m` FIXED, `γc` quantified
outside `L`, `ell₀`, `U`, `B` (uniform in the RG step `k`, which is what the recursion needs). -/
def CoarseCurlPoincareAtScale (m : ℕ) : Prop :=
  ∃ γc : ℝ, 0 < γc ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ : ℕ), 0 < ell₀ → 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      ∀ (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)),
        (∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1)) →
        ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell₀ * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (ell₀ * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (ell₀ * m), lineCoarseRestrictCov U (ell₀ * m) B c = 0) →
          γc * covCoarseBondInner (lineCoarseRestrictCovLM U ell₀ B)
              (lineCoarseRestrictCovLM U ell₀ B)
            ≤ coarseCurlEnergyCov hdvd₀ (coarseBackground U ell₀)
                (lineCoarseRestrictCovLM U ell₀ B)

/-- **The quantitative form**: one constant for every `m`, allowed to decay like `m^{-r}`. `r = 0`
is `CoarseCurlPoincareUniform` up to the flat/covariant replacement, and is REFUTED (§4). -/
def CoarseCurlPoincareScaled (r : ℕ) : Prop :=
  ∃ γc : ℝ, 0 < γc ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ m : ℕ), 0 < ell₀ → 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      ∀ (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)),
        (∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1)) →
        ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell₀ * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (ell₀ * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (ell₀ * m), lineCoarseRestrictCov U (ell₀ * m) B c = 0) →
          (γc / (m : ℝ) ^ r) * covCoarseBondInner (lineCoarseRestrictCovLM U ell₀ B)
              (lineCoarseRestrictCovLM U ell₀ B)
            ≤ coarseCurlEnergyCov hdvd₀ (coarseBackground U ell₀)
                (lineCoarseRestrictCovLM U ell₀ B)

/-- The scaled form implies the fixed-scale form at every `m ≥ 2` — so `r` measures exactly how
fast the constant is permitted to decay, and the refutations are lower bounds on `r`. -/
theorem scaled_imp_atScale {r : ℕ} (h : CoarseCurlPoincareScaled r) (m : ℕ) (hm : 2 ≤ m) :
    CoarseCurlPoincareAtScale m := by
  obtain ⟨γc, hγc, hall⟩ := h
  have hmpos : (0 : ℝ) < (m : ℝ) ^ r := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le two_pos hm
    positivity
  exact ⟨γc / (m : ℝ) ^ r, div_pos hγc hmpos,
    fun L ell₀ hell₀ _ hL hdvd₀ hdvdm U B hadm hker =>
      hall L ell₀ m hell₀ hm hL hdvd₀ hdvdm U B hadm hker⟩

/-- **THE GOAL LEMMA AT A FIXED COARSENING SCALE** — `γ₀`, `α₀` outside `L`, `ell₀`, `levels`, `U`,
`B`; `m` fixed. Uniform in the RG step, which is the uniformity the recursion consumes. -/
def Gamma0UniformTargetAtScale (m : ℕ) : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ : ℕ), 0 < ell₀ → 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      (∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) → (∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1)) →
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ (levels : List (KernelSubspace.Level L))
          [(CovariantHjMinimizer.deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful ell₀ levels U).HasOrthogonalProjection]
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell₀ * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (ell₀ * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (ell₀ * m), lineCoarseRestrictCov U (ell₀ * m) B c = 0) →
          γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell₀ B)
              (lineCoarseRestrictCovLM U ell₀ B)
            ≤ deltaJQuadFormCovFaithful ell₀ levels U B

/-- **THE REDUCTION SURVIVES THE SCALE CORRECTION.** `[SUMMED-TRANSFER-U-COV]` (the covariant
primitive 2) plus `CoarseCurlPoincareAtScale m` give the goal lemma at that `m`, with
`γ₀ = cT · γc`. This is `RegularUGamma0.gamma0UniformTarget_of_two_primitives` re-derived over the
covariant coarse curl and at a fixed coarsening — the argument never used `m`-uniformity, and it
never used the flat coarse curl except to have SOME common object between the two primitives, which
is now `coarseCurlEnergyCov`. -/
theorem gamma0AtScale_of_two_primitives (m : ℕ) :
    SummedTransferRegularUCov → CoarseCurlPoincareAtScale m → Gamma0UniformTargetAtScale m := by
  rintro ⟨cT, α₀, hcT, hα₀, htrans⟩ ⟨γc, hγc, hpoin⟩
  refine ⟨cT * γc, α₀, mul_pos hcT hγc, hα₀, ?_⟩
  intro L ell₀ hell₀ hm hL hdvd₀ hdvdm U hreg levels _ _ B hadm hker
  have h1 := hpoin L ell₀ hell₀ hm hL hdvd₀ hdvdm U B hadm hker
  have h2 := htrans L ell₀ hell₀ hdvd₀ U hreg levels B
  nlinarith [h1, h2, hcT]

/-- **The successor primitive is NOT vacuous**: its `(ell₀, m, U) = (1, 2, 1)` instance is the
already-proved one, transported to the covariant coarse curl by the `U = 1` control
(`coarseCurlEnergyCov_trivialU`). Same constant `1/1728`. -/
theorem coarseCurlPoincareAtScale_instance_one_two
    (L : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd₀ : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1))
    (hdvdm : ∀ μ : Fin 3, ((1 * 2 : ℕ)) ∣ (L μ + 1))
    (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (1 * 2) →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (1 * 2) →
      ∀ b ∈ staircasePath y x, B b = 0)
    (hker : ∀ c : CoarseBond L (1 * 2), lineCoarseRestrictCov (trivialU L) (1 * 2) B c = 0) :
    (1 / 1728 : ℝ) * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 1 B)
        (lineCoarseRestrictCovLM (trivialU L) 1 B)
      ≤ coarseCurlEnergyCov hdvd₀ (coarseBackground (trivialU L) 1)
          (lineCoarseRestrictCovLM (trivialU L) 1 B) := by
  rw [coarseCurlEnergyCov_trivialU]
  exact coarseCurlPoincare_body_at_one_two L hL hdvd₀ hdvdm B hadm hker

/-- **`r = 0` IS REFUTED** — the scaled form with NO decay is the original, and the `U = 1` case of
its covariant body is the flat one, so §4's witness applies verbatim. -/
theorem not_coarseCurlPoincareScaled_zero : ¬ CoarseCurlPoincareScaled 0 := by
  classical
  rintro ⟨γc, hγc, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / γc)
  set p := max 2 n with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hpn : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_max_right 2 n
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hkey := hall (witExt p) 1 (2 * p + 1) one_pos (by omega)
    (fun _ => by show 4 ≤ 2 * p; omega) (fun _ => one_dvd _)
    (fun _ => by rw [one_mul]; exact dvd_refl _) (trivialU _) (W1 p suTwoWitness)
    (by rw [one_mul]; exact fun y hy x _ b hb => W1_axial p suTwoWitness hy x b hb)
    (by rw [one_mul]; exact fun c => W1_kerQ p suTwoWitness c)
  rw [pow_zero, div_one, covCoarseBondInner_one_eq_bondEnergy, coarseCurlEnergyCov_trivialU,
    coarseCurlEnergySuTwo_one_eq_plaqEnergy, curl_trivialU_eq_flat] at hkey
  have hb := witness_forces_bound p (by omega) hw hkey
  have hgt : 3 < γc * (p : ℝ) := by
    rw [div_lt_iff₀ hγc] at hn
    nlinarith [hn, hpn, hγc]
  nlinarith [hb, hgt]

/-- **The scale correction is exactly what defuses THIS witness.** The W1 family SATISFIES the
scaled inequality at `r = 2` with `γc = 6`: `6/(2p+1)² · bondEnergy ≤ plaqEnergy` for every `p ≥ 1`.
So §4's refutation is a statement about the QUANTIFIER, not evidence against the successor.

**SUPERSEDED IN PART (2026-07-27), retained above verbatim.** The theorem is unchanged and true;
the final sentence is now correct only about §4's witness. There IS evidence against the successor,
from a DIFFERENT witness and a different mechanism: `CoarseCurlScaleTwo.not_coarseCurlPoincareScaled`
refutes the scaled form at every `r`, by a gauge-non-descent witness living at `ell₀ ≥ 2` (W1 lives
at `ell₀ = 1`, where the successor is in fact PROVED by §7). -/
theorem witness_satisfies_scaled_two (p : ℕ) (hp : 1 ≤ p) {w : SuTwo} (hw : w ≠ 0) :
    (6 / ((2 * p + 1 : ℕ) : ℝ) ^ 2) * bondEnergy (W1 p w)
      ≤ plaqEnergy (flatCurlValue (W1 p w)) := by
  have hrel := witness_energies p hp 2 1 (by decide) w
  have hpos := witness_plaq_pos p hp 2 1 (by decide) hw
  have hb : 0 ≤ bondEnergy (coordField (L := witExt p) 2 1 (witProfile p 1) w) := by
    unfold bondEnergy
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hmR : ((2 * p + 1 : ℕ) : ℝ) = 2 * (p : ℝ) + 1 := by push_cast; ring
  rw [show W1 p w = coordField (L := witExt p) 2 1 (witProfile p 1) w from rfl, hmR]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by nlinarith : (0:ℝ) < (2 * (p:ℝ) + 1) ^ 2)]
  nlinarith [hrel, hpos, hb, hpR]

/-! ## §7 — THE POSITIVE HALF: the successor primitive's `ell₀ = 1` case, PROVED AT EVERY `m`

The refutations say only that the constant may not be uniform in the block size. The tree's OWN
general-`ell` assembly says what the constant IS: `BlockPoincareSharp.sharp_size_bound` gives, for
every `ell ≥ 2` and every axial-gauge scalar field,

  `‖B‖² ≤ 3·ell⁵·‖Q_ell B‖² + bcoef(ell)·‖∂B‖²`,   `bcoef(ell) = 6ell² + (54ell²+1)(ell+1)(ell−1)²`,

which on `ker Q_ell` is exactly a Poincaré with constant `1/bcoef(ell) ≥ 1/(56·ell⁵)`.
~~— CMP96 (2.128)'s `ell^{-5}`.~~
**⚠ ATTRIBUTION CORRECTED 2026-07-27 (blind Kimi third gate). `ell^{-5}` is NOT the source's exponent;
it is OURS.** CMP96 (2.128) prints `L^{-d-1}`, i.e. **`ell^{-4}` at `d = 3`**. Three places in this tree
say so and said so before this file was written:
* `corpus/pages/CMP96_p245.md` (`verification_status: adjudicated`, re-rendered at 3600×5467 px to settle
  the two minus-strokes) reads `L^{-d-1}` unambiguously;
* `BlockPoincareLemma24.lemma24_constant_pin` PROVES `(1/108)·ell⁻⁴ = (1/(12·3²))·ell^{-(3+1)}`;
* `Lemma24GeneralEll.lean:105` states outright that `Lemma24ConclusionCorrected` is "(2.128) at `d = 3`
  with `L^{-d-1}` **replaced by**" the weaker exponent, and its §125 is headed *"why `ell^{-4}` is out of
  reach by this route"*, with `Lemma24Conclusion` recorded as NOT proved.
So `ell^{-5}` is the **weakened fallback we adopted because `ell^{-4}` was unreachable**. Calling it the
source's exponent makes this result sound closer to Bałaban than it is. The mathematics below is
unaffected — only the citation was wrong. §7 lifts the bound to the su(2) carrier through the three Pauli
components (all four bridges already exist in `SuTwoGeomU1`) and reads it as the `ell₀ = 1` case of
`CoarseCurlPoincareScaled 5`.

**Scope, stated exactly.** `sharp_size_bound` carries `hstrict : ell < L ν + 1` — strictly more than
one block per direction. `CoarseCurlPoincareScaled` does NOT carry that hypothesis, and §4's
refutation is built on a SINGLE-block torus, so §7 does not discharge the `def` even at `ell₀ = 1`;
it discharges its `hstrict` slice. (The refutation is not an artifact of the single block either:
repeating the profile block-periodically keeps every hypothesis and the same ratio — not compiled
here, and said as an observation, not a claim.)

**UPDATE (2026-07-27).** §7 is exactly the content that SURVIVES `CoarseCurlScaleTwo`: the
successor primitive holds at the fibre `ell₀ = 1` (this theorem) and fails at every `ell₀ ≥ 2`
(`CoarseCurlScaleTwo.scale_body_fails`). The `ell₀ ≥ 2` refutation is NOT a single-block artifact —
it is compiled on extents with two `(ell₀·m)`-blocks and `2m` `ell₀`-blocks per direction. -/

/-- **The su(2) lift of `BlockPoincareSharp.sharp_size_bound`**, coordinate-wise through the three
Pauli components, using only bridges that already exist (`SuTwoGeomU1.covBondInner_eq_sum`,
`covPlaqInner_flatCurl_eq_sum`, `covCoarseBondInner_lineCoarse_eq_sum`, `suComp_mem_admissible`). -/
theorem suTwo_sharp_size_bound {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0) :
    bondEnergy A
      ≤ 3 * (ell : ℝ) ^ 5 * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell A)
            (lineCoarseRestrictCovLM (trivialU L) ell A)
        + AdalyFormal.Balaban.BlockPoincareSharp.bcoef ell
            (AdalyFormal.Balaban.BlockPoincareSharp.blockPoincareSharpConst ell)
          * plaqEnergy (flatCurlValue A) := by
  classical
  have hQ : lineCoarseRestrictCovLM (trivialU L) ell A
      = (fun c => lineCoarseRestrictSuTwo ell A c) := by
    funext c
    rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU]
  rw [hQ, covCoarseBondInner_lineCoarse_eq_sum,
    ← AdalyFormal.Balaban.RegularUDirectCoercivity.covBondInner_eq_bondEnergy,
    covBondInner_eq_sum, ← covPlaqInner_self_eq_plaqEnergy, covPlaqInner_flatCurl_eq_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact AdalyFormal.Balaban.BlockPoincareSharp.sharp_size_bound hell2 hstrict hdvd
    (suComp i A) (suComp_mem_admissible ell i A hadm)

/-- `bcoef(m) ≤ 56·m⁵` for `m ≥ 2` — the explicit decay of the proved constant. -/
theorem bcoef_le (m : ℕ) (hm : 2 ≤ m) :
    AdalyFormal.Balaban.BlockPoincareSharp.bcoef m
        (AdalyFormal.Balaban.BlockPoincareSharp.blockPoincareSharpConst m)
      ≤ 56 * (m : ℝ) ^ 5 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold AdalyFormal.Balaban.BlockPoincareSharp.bcoef
    AdalyFormal.Balaban.BlockPoincareSharp.blockPoincareSharpConst
  nlinarith [hmR, sq_nonneg ((m : ℝ) - 2), sq_nonneg ((m : ℝ) - 1), pow_pos
    (lt_of_lt_of_le two_pos hmR) 3, pow_pos (lt_of_lt_of_le two_pos hmR) 5]

/-- **THE SUCCESSOR PRIMITIVE AT `ell₀ = 1`, EVERY `m ≥ 2`, WITH THE EXPLICIT CONSTANT `1/(56 m⁵)`.**
This is `CoarseCurlPoincareScaled 5`'s body at `ell₀ = 1`, `U = 1` (where the covariant coarse curl
IS the flat one), on the `hstrict` slice. It is the honest positive counterpart of §4: the
quantifier that fails is the one that demanded no decay at all, and the decay the tree can already
prove is `m^{-5}`.
~~— CMP96 (2.128)'s own exponent.~~ **STRUCK 2026-07-27: `m^{-5}` is OUR weakened fallback, not the
source's. CMP96 (2.128) prints `L^{-d-1}` = `ell^{-4}` at `d = 3`; see §6's corrected attribution and
`Lemma24GeneralEll` §125, "why `ell^{-4}` is out of reach by this route". The constant proved here is a
genuine positive result and is unaffected — but it sits one power FURTHER from the printed form than the
original wording claimed, not level with it.** -/
theorem coarseCurlPoincare_scaled_ell0_one {m : ℕ} (hm : 2 ≤ m)
    (hstrict : ∀ ν : Fin 3, m < L ν + 1) (hdvdm : ∀ ν : Fin 3, m ∣ (L ν + 1))
    (hdvd1 : ∀ ν : Fin 3, (1 : ℕ) ∣ (L ν + 1)) (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L m →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y m → ∀ b ∈ staircasePath y x, B b = 0)
    (hker : ∀ c : CoarseBond L m, lineCoarseRestrictCov (trivialU L) m B c = 0) :
    ((1 : ℝ) / 56 / (m : ℝ) ^ 5)
        * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 1 B)
          (lineCoarseRestrictCovLM (trivialU L) 1 B)
      ≤ coarseCurlEnergyCov hdvd1 (coarseBackground (trivialU L) 1)
          (lineCoarseRestrictCovLM (trivialU L) 1 B) := by
  classical
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm5 : (0 : ℝ) < (m : ℝ) ^ 5 := by positivity
  -- the coarse term of the assembly vanishes on `ker Q_m`
  have hz : lineCoarseRestrictCovLM (trivialU L) m B = 0 := by
    funext c
    rw [lineCoarseRestrictCovLM_apply]
    exact hker c
  have hzero : covCoarseBondInner (0 : CoarseBond L m → SuTwo) 0 = 0 := by
    unfold covCoarseBondInner
    simp only [Pi.zero_apply, CovariantHj.hsInner_zero_zero, Finset.sum_const_zero]
  have hbase := suTwo_sharp_size_bound hm hstrict hdvdm B hadm
  rw [hz, hzero, mul_zero, zero_add] at hbase
  -- read both sides at `ell₀ = 1`
  rw [coarseCurlEnergyCov_trivialU, coarseCurlEnergySuTwo_one_eq_plaqEnergy,
    curl_trivialU_eq_flat, covCoarseBondInner_one_eq_bondEnergy]
  have hbc := bcoef_le m hm
  have hplaq : 0 ≤ plaqEnergy (flatCurlValue B) := by
    unfold plaqEnergy
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 56 * (m : ℝ) ^ 5)]
  nlinarith [hbase, hbc, hplaq]

/-! ## §A — AXIOM AUDIT: `#print axioms` on EVERY declaration of this module (65 of them) -/

#print axioms coordScalar
#print axioms coordField
#print axioms coordField_apply
#print axioms shift_coord_ne
#print axioms shiftBack_coord_ne
#print axioms shiftIter_coord_ne
#print axioms shift_coord_self
#print axioms sum_site_coord
#print axioms card_other_coords_pos
#print axioms norm_sq_coordField
#print axioms bondEnergy_coordField
#print axioms flatCurl_coordField
#print axioms plaqEnergy_coordField
#print axioms Q_coordField
#print axioms div_coordField
#print axioms sqN
#print axioms sqProfile
#print axioms sqProfile_zero
#print axioms sum_sqN
#print axioms sum_sqN_sq
#print axioms sum_sqProfile
#print axioms sum_sqProfile_sq
#print axioms zeroIdx
#print axioms pIdx
#print axioms p2Idx
#print axioms zeroIdx_val
#print axioms pIdx_val
#print axioms p2Idx_val
#print axioms sqProfile_diff_sq
#print axioms sum_sqProfile_diff
#print axioms witExt
#print axioms witExt_apply
#print axioms witProfile
#print axioms witProfile_zero
#print axioms sum_witProfile
#print axioms sum_witProfile_sq
#print axioms sum_witProfile_diff
#print axioms coarse_site_zero
#print axioms block_univ
#print axioms witness_kerQ
#print axioms witness_energies
#print axioms witness_plaq_pos
#print axioms W1
#print axioms W1_axial
#print axioms W1_kerQ
#print axioms curl_trivialU_eq_flat
#print axioms witness_forces_bound
#print axioms not_coarseCurlPoincareUniform
#print axioms not_gamma0TrivialUTarget
#print axioms not_gamma0UniformTarget
#print axioms W3
#print axioms W3_kerQ
#print axioms W3_divFree
#print axioms not_kerQDivFreePoincare
#print axioms CoarseCurlPoincareAtScale
#print axioms CoarseCurlPoincareScaled
#print axioms scaled_imp_atScale
#print axioms Gamma0UniformTargetAtScale
#print axioms gamma0AtScale_of_two_primitives
#print axioms coarseCurlPoincareAtScale_instance_one_two
#print axioms not_coarseCurlPoincareScaled_zero
#print axioms witness_satisfies_scaled_two
#print axioms suTwo_sharp_size_bound
#print axioms bcoef_le
#print axioms coarseCurlPoincare_scaled_ell0_one

end AdalyFormal.Balaban.CoarseCurlPoincare
