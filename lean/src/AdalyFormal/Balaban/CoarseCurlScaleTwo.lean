/-
Copyright (c) 2026 Project Adaly. All rights reserved.
-/
import AdalyFormal.Balaban.CoarseCurlPoincare

/-!
# `[COARSE-CURL-POINCARE-AT-SCALE]` at `ell₀ ≥ 2` — the scale correction does NOT rescue it

`CoarseCurlPoincare` established two facts about the coarse-curl Poincaré primitive:

* the **scale-UNIFORM** form is FALSE (`not_coarseCurlPoincareUniform` and siblings): a field
  oscillating on the block scale has curl energy `~ blocksize⁻²` times its bond energy;
* the **scale-corrected** successor `CoarseCurlPoincareAtScale m` / `CoarseCurlPoincareScaled r`
  HOLDS at the fibre `ell₀ = 1`, at every `m ≥ 2`, with the source's own constant `1/(56·m⁵)`
  (`coarseCurlPoincare_scaled_ell0_one`), and the reduction to the goal lemma survives the
  correction (`gamma0AtScale_of_two_primitives`).

This module settles the remaining fibre, `ell₀ ≥ 2`, and the answer is NEGATIVE: the successor is
false there, for a reason that has nothing to do with the constant's scale dependence.

## The mechanism — the fine axial gauge does not descend to the coarse lattice

`AdmissibleSubspace.staircasePath` walks the order `(2, 1, 0)`. Its direction-`2` segment sits on a
single LINE (coordinates `0` and `1` are pinned to the block corner `y`), so the axial-gauge clause
of the primitive constrains a direction-`2` field only on that line. The coarse average `Q_{ell₀}B`
therefore inherits NO gauge condition at all, and can be a nonzero coarse field whose coarse curl
vanishes identically. Then the primitive's left-hand side is positive and its right-hand side is
`0`, at EVERY constant — so no scale correction can help, and `m` is irrelevant.

## The witness (§2–§6)

Parameters: a fine block side `e = ell₀ ≥ 2`, a constraint level `n` with `e ∣ n` and `2e ≤ n`
(`n = ell₀·m`, `m ≥ 2`), and ANY extent with `n ∣ (L μ + 1)` — arbitrarily many blocks per
direction at BOTH levels, so nothing below is a single-block artifact. Background `U = 1`.

  `ψ(z) := [ (z 1).val % e = 1 ] · [ (z 2).val % n = 0 ]`
  `B(b) := if b.2 = 2 then (ψ(b.1 + e₂) − ψ(b.1))·w else 0`

`B` is the direction-`2` DISCRETE GRADIENT of `ψ`, carried on direction-`2` bonds only. That single
design choice removes both pieces of machinery a naive witness would need:

* every direction-`2` line integral **telescopes** (`scField_lineSum`), so membership in `ker Q_n`
  is immediate from the `n`-periodicity of `ψ` in direction `2` (`psiSc_coarseShift_n`) — no
  full-period summation lemma, and no need for the torus to be a single `n`-block;
* the coarse curl vanishes **term by term**: the only differences the curl of a direction-`2`-only
  coarse field can see are `Q_eB(y + e·e_ν, 2) − Q_eB(y, 2)` for `ν ∈ {0,1}`, and block translation
  (`CoarseShiftCovariance.coarseShift_blockOf_eq_image`) plus the POINTWISE invariance
  `ψ(z + e·e_ν) = ψ(z)` (`ψ` reads coordinate `1` only through `% e`, and `e ∣ L 1 + 1`) kills each
  summand — no block-sum factorization;
* nonvanishing of `Q_eB` needs no evaluation either: on the origin `e`-block every summand is
  NONPOSITIVE (`ψ(x + e·e_2) = 0` there, since `(x 2).val + e` lies strictly between `0` and `n`)
  and the summand at `x* = (0,1,0)` equals `−1`, so the block sum is strictly negative
  (`scBlockSum_origin_neg`).

## What is established, exactly

* `scale_body_fails` — the BODY of the primitive is false at every `ell₀ = e ≥ 2`, every constraint
  level `n` with `e ∣ n` and `2e ≤ n`, and every extent with `n ∣ (L μ + 1)`.
* `not_coarseCurlPoincareAtScale : ∀ m, 2 ≤ m → ¬ CoarseCurlPoincareAtScale m`
* `not_coarseCurlPoincareScaled : ∀ r, ¬ CoarseCurlPoincareScaled r` — every decay rate, including
  the `r = 5` that `coarseCurlPoincare_scaled_ell0_one` proves AT `ell₀ = 1`. So the compiled
  exponent bracket `1 ≤ r ≤ 5` recorded by the previous lane does not close: NO exponent works.
* §8, separately: the exponent bracket for the fibre that DOES survive. `CoarseCurlPoincareFibreOne
  r` is the body of `CoarseCurlPoincareScaled r` with `ell₀ := 1` verbatim
  (`fibreOne_of_scaled`), and `not_coarseCurlPoincareFibreOne_one` refutes it at `r = 1` with a
  periodic SAWTOOTH. With `coarseCurlPoincare_scaled_ell0_one` at the top end, the compiled bracket
  for the surviving fibre tightens from `1 ≤ r ≤ 5` to **`2 ≤ r ≤ 5`**. (The upper end carries
  `hstrict`; the lower-end refutations live on a single-block torus. That asymmetry is inherited
  from the previous lane, stated, and not repaired here.)

So the honest state of the route: **the primitive holds at `ell₀ = 1` and fails at every
`ell₀ ≥ 2`.** The reduction `gamma0AtScale_of_two_primitives` remains a valid implication, but its
second antecedent is false, so the reduction does not deliver the goal lemma as a general route.

**What this is NOT.** It is not evidence about Bałaban's own (2.128). It is evidence about the Prop
as stated in this tree, and it localizes the defect: the axial-gauge hypothesis is imposed at the
COARSE constraint level `ell₀·m` while the conclusion is read at the FINE level `ell₀`, and the
`(2,1,0)` staircase gauge does not descend. A repaired statement must either impose a gauge
condition on the COARSE field `Q_{ell₀}B` itself, or read the conclusion at the same level at which
the gauge is imposed. Neither repair is attempted here.
-/

namespace AdalyFormal.Balaban.CoarseCurlScaleTwo

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseShift coarseShift_mem_coarseLattice
  coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)
open AdalyFormal.Balaban.FourierFaithfulU1 (coarseShift_coarseShift_comm)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy)
open AdalyFormal.Balaban.RegularUGamma0 (coarseCurlEnergySuTwo
  covCoarseBondInner_one_eq_bondEnergy coarseCurlEnergySuTwo_one_eq_plaqEnergy)
open AdalyFormal.Balaban.CoarseCurlCovariant
open AdalyFormal.Balaban.CoarseCurlPoincare

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the potential `ψ` and the witness field

`ψ` reads coordinate `1` only through `% e` and coordinate `2` only through `% n`. Those two facts
are the whole construction: the first gives the coarse-curl cancellation, the second gives
membership in `ker Q_n`. -/

/-- **The potential.** `1` exactly on the sites whose coordinate `1` is `≡ 1 (mod e)` and whose
coordinate `2` is `≡ 0 (mod n)`; `0` elsewhere. -/
noncomputable def psiSc (e n : ℕ) (z : PeriodicLatticeSite L) : ℝ :=
  if (z 1).val % e = 1 ∧ (z 2).val % n = 0 then 1 else 0

theorem psiSc_nonneg (e n : ℕ) (z : PeriodicLatticeSite L) : 0 ≤ psiSc e n z := by
  unfold psiSc; split <;> norm_num

theorem psiSc_eq_zero_of_coord1 {e n : ℕ} {z : PeriodicLatticeSite L} (h : (z 1).val % e ≠ 1) :
    psiSc e n z = 0 := by
  unfold psiSc; rw [if_neg]; exact fun hc => h hc.1

/-- **The witness field**: the direction-`2` discrete gradient of `ψ`, carried on direction-`2`
bonds only. Every one of its direction-`2` line integrals telescopes. -/
noncomputable def scField (e n : ℕ) (w : SuTwo) : Bond L → SuTwo :=
  fun b => if b.2 = 2 then (psiSc e n (periodicLatticeShift b.1 2) - psiSc e n b.1) • w else 0

theorem scField_dir_ne {e n : ℕ} {w : SuTwo} {b : Bond L} (h : b.2 ≠ 2) :
    scField e n w b = 0 := by
  unfold scField; rw [if_neg h]

/-- The field vanishes wherever the base site's coordinate `1` is not `≡ 1 (mod e)` — the clause
that discharges the axial gauge (the staircase's direction-`2` segment pins coordinate `1` to the
block corner's value, which is a multiple of `e`). -/
theorem scField_eq_zero_of_coord1 {e n : ℕ} (w : SuTwo) {b : Bond L}
    (h : (b.1 1).val % e ≠ 1) : scField e n w b = 0 := by
  unfold scField
  by_cases hb : b.2 = 2
  · rw [if_pos hb]
    have h2 : psiSc e n (periodicLatticeShift b.1 2) = 0 := by
      refine psiSc_eq_zero_of_coord1 ?_
      rw [shift_coord_ne (by decide : (1 : Fin 3) ≠ 2) b.1]
      exact h
    rw [psiSc_eq_zero_of_coord1 h, h2, sub_self, zero_smul]
  · rw [if_neg hb]

/-! ## §2 — the two invariances of `ψ` -/

/-- Coordinate `1`, read mod `e`, is invariant under EVERY coarse translation by `e` (in direction
`1` because `e ∣ L 1 + 1`; in the other directions because the coordinate does not move). -/
theorem coord1_mod_coarseShift {e : ℕ} (hdvd1 : e ∣ (L 1 + 1)) (ν : Fin 3)
    (z : PeriodicLatticeSite L) : ((coarseShift z e ν) 1).val % e = (z 1).val % e := by
  by_cases h : (1 : Fin 3) = ν
  · subst h
    rw [coarseShift_val_eq, Nat.mod_mod_of_dvd _ hdvd1, Nat.add_mod_right]
  · rw [coarseShift_apply_ne z e ν 1 h]

/-- **INVARIANCE (a)**: `ψ` is unchanged by the coarse translation by `e` in directions `0` and `1`.
This is what makes the coarse curl vanish term by term. -/
theorem psiSc_coarseShift {e n : ℕ} (hdvd1 : e ∣ (L 1 + 1)) {ν : Fin 3} (hν : ν ≠ 2)
    (z : PeriodicLatticeSite L) : psiSc e n (coarseShift z e ν) = psiSc e n z := by
  have h1 : ((coarseShift z e ν) 1).val % e = (z 1).val % e := coord1_mod_coarseShift hdvd1 ν z
  have h2 : ((coarseShift z e ν) 2).val = (z 2).val := by
    rw [coarseShift_apply_ne z e ν 2 (Ne.symm hν)]
  unfold psiSc
  by_cases hc : (z 1).val % e = 1 ∧ (z 2).val % n = 0
  · rw [if_pos (by rw [h1, h2]; exact hc), if_pos hc]
  · rw [if_neg (by rw [h1, h2]; exact hc), if_neg hc]

/-- **INVARIANCE (b)**: `ψ` is unchanged by the coarse translation by `n` in direction `2`, provided
`n ∣ L 2 + 1`. This is what puts the field in `ker Q_n`, WITHOUT requiring the torus to be a single
`n`-block. -/
theorem psiSc_coarseShift_n {e n : ℕ} (hdvd2 : n ∣ (L 2 + 1)) (z : PeriodicLatticeSite L) :
    psiSc e n (coarseShift z n 2) = psiSc e n z := by
  have h1 : ((coarseShift z n 2) 1).val = (z 1).val := by
    rw [coarseShift_apply_ne z n 2 1 (by decide : (1 : Fin 3) ≠ 2)]
  have h2 : ((coarseShift z n 2) 2).val % n = (z 2).val % n := by
    rw [coarseShift_val_eq, Nat.mod_mod_of_dvd _ hdvd2, Nat.add_mod_right]
  unfold psiSc
  by_cases hc : (z 1).val % e = 1 ∧ (z 2).val % n = 0
  · rw [if_pos (by rw [h1, h2]; exact hc), if_pos hc]
  · rw [if_neg (by rw [h1, h2]; exact hc), if_neg hc]

/-! ## §3 — the coarse average of the witness field, in closed form -/

/-- The block sum of the telescoped direction-`2` line integral. -/
noncomputable def scBlockSum (e n ell : ℕ) (y : PeriodicLatticeSite L) : ℝ :=
  ∑ x ∈ blockOf y ell, (psiSc e n (coarseShift x ell 2) - psiSc e n x)

/-- **The telescoping.** The direction-`2` line integral of `scField` over `ell` steps is the
endpoint difference of `ψ`. -/
theorem scField_lineSum (e n ell : ℕ) (w : SuTwo) (x : PeriodicLatticeSite L) :
    (∑ i ∈ Finset.range ell, scField e n w (pathSite x (2 : Fin 3) i, (2 : Fin 3)))
      = (psiSc e n (coarseShift x ell 2) - psiSc e n x) • w := by
  have hterm : ∀ i ∈ Finset.range ell,
      scField e n w (pathSite x (2 : Fin 3) i, (2 : Fin 3))
        = (psiSc e n (pathSite x (2 : Fin 3) (i + 1)) • w)
          - (psiSc e n (pathSite x (2 : Fin 3) i) • w) := by
    intro i _
    unfold scField
    rw [if_pos rfl, pathSite_succ, sub_smul]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub (fun i => psiSc e n (pathSite x (2 : Fin 3) i) • w) ell,
    pathSite_zero, sub_smul]
  rfl

/-- **`Q_ell(1)` of the witness field, closed form**: supported on direction-`2` coarse bonds,
where it is `(1/ell⁴)` times the block sum of the telescoped line integral. -/
theorem scField_Q (e n ell : ℕ) (w : SuTwo) (c : CoarseBond L ell) :
    lineCoarseRestrictCov (trivialU L) ell (scField e n w) c
      = ((1 / (ell : ℝ) ^ 4) * (if c.2 = 2 then scBlockSum e n ell c.1.1 else 0)) • w := by
  rw [lineCoarseRestrictCov_trivialU]
  unfold lineCoarseRestrictSuTwo
  by_cases hc : c.2 = 2
  · rw [if_pos hc]
    have hx : ∀ x ∈ blockOf c.1.1 ell,
        (∑ i ∈ Finset.range ell, scField e n w (pathSite x c.2 i, c.2))
          = (psiSc e n (coarseShift x ell 2) - psiSc e n x) • w := by
      intro x _
      rw [hc]
      exact scField_lineSum e n ell w x
    rw [Finset.sum_congr rfl hx, ← Finset.sum_smul, mul_smul]
    rfl
  · rw [if_neg hc, mul_zero, zero_smul]
    have hx : ∀ x ∈ blockOf c.1.1 ell,
        (∑ i ∈ Finset.range ell, scField e n w (pathSite x c.2 i, c.2)) = 0 := by
      intro x _
      exact Finset.sum_eq_zero fun i _ => scField_dir_ne hc
    rw [Finset.sum_congr rfl hx, Finset.sum_const_zero, smul_zero]

/-- The coarse average of the witness field at the FINE level `e`, as a named coarse field (so that
`coarseCurlSuTwo` unfolds to applications of a constant, not to beta-redexes). -/
noncomputable def scQ (e n : ℕ) (w : SuTwo) : CoarseBond L e → SuTwo :=
  fun c => lineCoarseRestrictCov (trivialU L) e (scField e n w) c

theorem scQ_eq_LM (e n : ℕ) (w : SuTwo) :
    (lineCoarseRestrictCovLM (trivialU L) e (scField e n w) : CoarseBond L e → SuTwo)
      = scQ e n w := by
  funext c
  rw [lineCoarseRestrictCovLM_apply]
  rfl

theorem scQ_dir2 (e n : ℕ) (w : SuTwo) (c : CoarseBond L e) (hc : c.2 = 2) :
    scQ e n w c = ((1 / (e : ℝ) ^ 4) * scBlockSum e n e c.1.1) • w := by
  unfold scQ
  rw [scField_Q, if_pos hc]

theorem scQ_dir_ne (e n : ℕ) (w : SuTwo) (c : CoarseBond L e) (hc : c.2 ≠ 2) :
    scQ e n w c = 0 := by
  unfold scQ
  rw [scField_Q, if_neg hc, mul_zero, zero_smul]

/-! ## §4 — the two gauge-side clauses: axial at level `n`, and `ker Q_n` -/

/-- **AXIAL at the constraint level `n`.** The staircase's direction-`2` segment pins coordinate `1`
to the coarse corner's value, which is a multiple of `n` hence of `e`, so `ψ` vanishes at both ends
of every direction-`2` bond on that segment. The direction-`0` and direction-`1` segments carry no
field at all. NOTE: no hypothesis on the extent — this holds on every torus. -/
theorem scField_axial {e n : ℕ} (w : SuTwo) (hedvd : e ∣ n)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L n)
    (x : PeriodicLatticeSite L) (b : PeriodicLatticeEdge L) (hb : b ∈ staircasePath y x) :
    scField e n w b = 0 := by
  have hy1 : (y 1).val % e = 0 := by
    have h1 := (mem_CoarseLattice.mp hy) 1
    obtain ⟨k, hk⟩ := dvd_trans hedvd (Nat.dvd_of_mod_eq_zero h1)
    rw [hk]
    exact Nat.mul_mod_right e k
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (hb | hb) | hb
  · -- direction-2 segment based at `y`
    rw [mem_axisSegment] at hb
    refine scField_eq_zero_of_coord1 w ?_
    rw [hb.2.1 1 (by decide), hy1]
    omega
  · -- direction-1 segment
    rw [mem_axisSegment] at hb
    exact scField_dir_ne (by rw [hb.1]; decide)
  · -- direction-0 segment
    rw [mem_axisSegment] at hb
    exact scField_dir_ne (by rw [hb.1]; decide)

/-- **`ker Q_n`.** Every block sum at level `n` vanishes, by the `n`-periodicity of `ψ` in
direction `2`. -/
theorem scField_kerQ {e n : ℕ} (w : SuTwo) (hdvd2 : n ∣ (L 2 + 1))
    (c : CoarseBond L n) : lineCoarseRestrictCov (trivialU L) n (scField e n w) c = 0 := by
  rw [scField_Q]
  have hzero : scBlockSum e n n c.1.1 = 0 := by
    unfold scBlockSum
    exact Finset.sum_eq_zero fun x _ => by rw [psiSc_coarseShift_n hdvd2 x, sub_self]
  rw [hzero]
  simp

/-! ## §5 — the coarse curl of `Q_e B` vanishes identically -/

/-- **The block sum is invariant under the coarse translation by `e` in directions `0` and `1`** —
by block translation plus the pointwise invariance of `ψ`. No block-sum factorization. -/
theorem scBlockSum_coarseShift {e n : ℕ} (he : 0 < e) (hdvd : ∀ μ : Fin 3, e ∣ (L μ + 1))
    {ν : Fin 3} (hν : ν ≠ 2) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L e) :
    scBlockSum e n e (coarseShift y e ν) = scBlockSum e n e y := by
  unfold scBlockSum
  rw [coarseShift_blockOf_eq_image he (hdvd ν) hy,
    Finset.sum_image (fun a _ b _ h => coarseShift_injective e ν h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcomm : coarseShift (coarseShift x e ν) e 2 = coarseShift (coarseShift x e 2) e ν :=
    coarseShift_coarseShift_comm x e e (Ne.symm hν)
  rw [hcomm, psiSc_coarseShift (hdvd 1) hν, psiSc_coarseShift (hdvd 1) hν]

/-- **THE COARSE CURL OF `Q_e B` IS IDENTICALLY ZERO.** The coarse field is direction-`2`-only and
its direction-`2` component is invariant under coarse translation in directions `0` and `1`; those
are the only two comparisons a coarse curl of such a field can make. -/
theorem scField_coarseCurl_zero {e n : ℕ} (he : 0 < e) (hdvd : ∀ μ : Fin 3, e ∣ (L μ + 1))
    (w : SuTwo) (p : CoarsePlaquette L e) :
    coarseCurlSuTwo hdvd (scQ e n w) p = 0 := by
  have hab : (p.2.1.1 : Fin 3) < p.2.1.2 := p.2.2
  have ha2 : (p.2.1.1 : Fin 3) ≠ 2 := by
    intro hc
    have h1 : (p.2.1.1 : Fin 3).val = 2 := by rw [hc]; rfl
    have h2 : (p.2.1.1 : Fin 3).val < (p.2.1.2 : Fin 3).val := hab
    have h3 : (p.2.1.2 : Fin 3).val < 3 := p.2.1.2.isLt
    omega
  -- the four bonds the coarse curl reads, written out so `rw` cannot pick the wrong occurrence
  set c1 : CoarseBond L e := (p.1, p.2.1.1) with hc1
  set c2 : CoarseBond L e :=
    (⟨coarseShift p.1.1 e p.2.1.1, coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.1⟩,
      p.2.1.2) with hc2
  set c3 : CoarseBond L e :=
    (⟨coarseShift p.1.1 e p.2.1.2, coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.2⟩,
      p.2.1.1) with hc3
  set c4 : CoarseBond L e := (p.1, p.2.1.2) with hc4
  have hd1 : c1.2 ≠ 2 := ha2
  have hd3 : c3.2 ≠ 2 := ha2
  change scQ e n w c1 + scQ e n w c2 - scQ e n w c3 - scQ e n w c4 = 0
  by_cases hb2 : (p.2.1.2 : Fin 3) = 2
  · have hd2 : c2.2 = 2 := hb2
    have hd4 : c4.2 = 2 := hb2
    have hinv : scBlockSum e n e c2.1.1 = scBlockSum e n e c4.1.1 :=
      scBlockSum_coarseShift he hdvd ha2 p.1.2
    rw [scQ_dir_ne e n w c1 hd1, scQ_dir_ne e n w c3 hd3, scQ_dir2 e n w c2 hd2,
      scQ_dir2 e n w c4 hd4, hinv]
    abel
  · -- `p.2.1.1 < p.2.1.2 ≠ 2` forces both directions into `{0,1}`
    have hd2 : c2.2 ≠ 2 := hb2
    have hd4 : c4.2 ≠ 2 := hb2
    rw [scQ_dir_ne e n w c1 hd1, scQ_dir_ne e n w c2 hd2, scQ_dir_ne e n w c3 hd3,
      scQ_dir_ne e n w c4 hd4]
    abel

/-- …hence the covariant coarse-curl energy at `U = 1` vanishes. -/
theorem scField_coarseCurlEnergy_zero {e n : ℕ} (he : 0 < e) (hdvd : ∀ μ : Fin 3, e ∣ (L μ + 1))
    (w : SuTwo) :
    coarseCurlEnergyCov hdvd (coarseBackground (trivialU L) e)
        (lineCoarseRestrictCovLM (trivialU L) e (scField e n w)) = 0 := by
  rw [coarseCurlEnergyCov_trivialU]
  unfold coarseCurlEnergySuTwo
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [scQ_eq_LM e n w, scField_coarseCurl_zero he hdvd w p, hsInner_zero_zero]

/-! ## §6 — `Q_e B` is NOT zero -/

/-- The corner of the origin block. -/
def scOrigin (L : PeriodicLatticeExtent) : PeriodicLatticeSite L := fun _ => 0

theorem scOrigin_val (μ : Fin 3) : ((scOrigin L) μ).val = 0 := rfl

/-- The site `(0, 1, 0)` — the single point of the origin `e`-block where `ψ = 1`. -/
def scStar {L : PeriodicLatticeExtent} (h : ∀ μ : Fin 3, 1 < L μ + 1) : PeriodicLatticeSite L :=
  fun μ => if μ = 1 then ⟨1, h μ⟩ else 0

theorem scStar_val {h : ∀ μ : Fin 3, 1 < L μ + 1} (μ : Fin 3) :
    ((scStar h : PeriodicLatticeSite L) μ).val = if μ = 1 then 1 else 0 := by
  unfold scStar
  by_cases hμ : μ = 1
  · rw [if_pos hμ, if_pos hμ]
  · rw [if_neg hμ, if_neg hμ]
    rfl

theorem scOrigin_mem_coarse {e : ℕ} : (scOrigin L) ∈ CoarseLattice L e := by
  rw [mem_CoarseLattice]
  intro μ
  rw [scOrigin_val]
  exact Nat.zero_mod e

/-- On the origin `e`-block every summand of the block sum is nonpositive, and the summand at
`x* = (0,1,0)` is `−1`. So the block sum is strictly negative — no evaluation of the block sum is
needed, only its sign. -/
theorem scBlockSum_origin_neg {e n : ℕ} (he : 2 ≤ e) (h2e : 2 * e ≤ n)
    (hdvdn : ∀ μ : Fin 3, n ∣ (L μ + 1)) :
    scBlockSum (L := L) e n e (scOrigin L) < 0 := by
  have hnle : ∀ μ : Fin 3, n ≤ L μ + 1 := fun μ => Nat.le_of_dvd (Nat.succ_pos _) (hdvdn μ)
  have hlt : ∀ μ : Fin 3, 1 < L μ + 1 := by
    intro μ
    have := hnle μ
    omega
  -- the "top" term of every summand vanishes on the origin block
  have htop : ∀ x ∈ blockOf (scOrigin L) e, psiSc e n (coarseShift x e 2) = 0 := by
    intro x hx
    have hx2 : (x 2).val < e := by
      have h := (mem_blockOf.mp hx) 2
      rw [scOrigin_val] at h
      omega
    have hval : ((coarseShift x e 2) 2).val = (x 2).val + e := by
      rw [coarseShift_val_eq]
      refine Nat.mod_eq_of_lt ?_
      have := hnle 2
      omega
    unfold psiSc
    rw [if_neg]
    rintro ⟨-, hc2⟩
    rw [hval, Nat.mod_eq_of_lt (by omega)] at hc2
    omega
  have hstar : (scStar hlt : PeriodicLatticeSite L) ∈ blockOf (scOrigin L) e := by
    rw [mem_blockOf]
    intro μ
    rw [scOrigin_val, scStar_val]
    by_cases hμ : μ = 1
    · rw [if_pos hμ]; omega
    · rw [if_neg hμ]; omega
  have hpsistar : psiSc (L := L) e n (scStar hlt) = 1 := by
    unfold psiSc
    rw [if_pos]
    refine ⟨?_, ?_⟩
    · rw [scStar_val, if_pos rfl]
      exact Nat.mod_eq_of_lt he
    · rw [scStar_val, if_neg (by decide : ¬ ((2 : Fin 3) = 1))]
      exact Nat.zero_mod n
  refine lt_of_lt_of_le ?_ (le_of_eq (Finset.sum_const_zero (s := blockOf (scOrigin L) e)))
  unfold scBlockSum
  refine Finset.sum_lt_sum ?_ ⟨scStar hlt, hstar, ?_⟩
  · intro x hx
    rw [htop x hx, zero_sub, neg_nonpos]
    exact psiSc_nonneg e n x
  · rw [htop _ hstar, zero_sub, neg_lt_zero, hpsistar]
    norm_num

/-- **`Q_e B ≠ 0`**, hence its coarse `L²` norm is strictly positive — the primitive's left-hand
side. -/
theorem scField_Q_norm_pos {e n : ℕ} (he : 2 ≤ e) (h2e : 2 * e ≤ n)
    (hdvdn : ∀ μ : Fin 3, n ∣ (L μ + 1)) {w : SuTwo} (hw : w ≠ 0) :
    0 < covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))
      (lineCoarseRestrictCovLM (trivialU L) e (scField e n w)) := by
  refine covCoarseBondInner_pos_of_ne ?_
  intro hcontra
  have hval := congrFun hcontra
    ((⟨scOrigin L, scOrigin_mem_coarse⟩, (2 : Fin 3)) : CoarseBond L e)
  rw [scQ_eq_LM e n w, scQ_dir2 e n w _ rfl, Pi.zero_apply] at hval
  have hneg := scBlockSum_origin_neg (L := L) he h2e hdvdn
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast lt_of_lt_of_le two_pos he
  have h4 : (0 : ℝ) < (e : ℝ) ^ 4 := pow_pos hepos 4
  have hcoef : (1 / (e : ℝ) ^ 4) * scBlockSum (L := L) e n e (scOrigin L) ≠ 0 :=
    mul_ne_zero (ne_of_gt (one_div_pos.mpr h4)) (ne_of_lt hneg)
  rcases smul_eq_zero.mp hval with h | h
  · exact hcoef h
  · exact hw h

/-! ## §7 — THE REFUTATIONS -/

/-- **THE BODY OF THE SUCCESSOR PRIMITIVE FAILS AT EVERY `ell₀ = e ≥ 2`**, at every constraint
level `n` with `e ∣ n` and `2e ≤ n` (i.e. `n = e·m`, `m ≥ 2`), on EVERY extent with
`n ∣ (L μ + 1)` — arbitrarily many blocks per direction at both levels. The right-hand side is `0`
and the left-hand side is strictly positive at every `γc > 0`. -/
theorem scale_body_fails {e n : ℕ} (he : 2 ≤ e) (h2e : 2 * e ≤ n)
    {L : PeriodicLatticeExtent} (hdvdn : ∀ μ : Fin 3, n ∣ (L μ + 1))
    (hdvd₀ : ∀ μ : Fin 3, e ∣ (L μ + 1)) {γc : ℝ} (hγc : 0 < γc) {w : SuTwo} (hw : w ≠ 0) :
    ¬ (γc * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))
          (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))
        ≤ coarseCurlEnergyCov hdvd₀ (coarseBackground (trivialU L) e)
            (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))) := by
  have hepos : 0 < e := lt_of_lt_of_le two_pos he
  have hpos := scField_Q_norm_pos (L := L) he h2e hdvdn hw
  rw [scField_coarseCurlEnergy_zero (L := L) hepos hdvd₀ w]
  exact not_le.mpr (mul_pos hγc hpos)

/-- The witness extent: `L μ + 1 = 6·m` in every direction, i.e. TWO blocks per direction at the
constraint level `3m` and `2m` blocks per direction at the fine level `3`. -/
def scExt (m : ℕ) : PeriodicLatticeExtent := fun _ => 6 * m - 1

theorem scExt_add_one {m : ℕ} (h : 1 ≤ m) (μ : Fin 3) : scExt m μ + 1 = 6 * m := by
  unfold scExt
  omega

/-- **`CoarseCurlPoincareAtScale m` IS FALSE, at every `m ≥ 2`.** Refuted at `ell₀ = 3` on a torus
with two `(3m)`-blocks per direction; `scale_body_fails` shows any `ell₀ ≥ 2` and any number of
blocks works. -/
theorem not_coarseCurlPoincareAtScale (m : ℕ) (hm : 2 ≤ m) : ¬ CoarseCurlPoincareAtScale m := by
  classical
  rintro ⟨γc, hγc, hall⟩
  have hL : ∀ μ : Fin 3, scExt m μ + 1 = 6 * m := fun μ => scExt_add_one (by omega) μ
  have hdvd₀ : ∀ μ : Fin 3, (3 : ℕ) ∣ (scExt m μ + 1) := by
    intro μ; rw [hL μ]; exact ⟨2 * m, by ring⟩
  have hdvdm : ∀ μ : Fin 3, ((3 * m : ℕ)) ∣ (scExt m μ + 1) := by
    intro μ; rw [hL μ]; exact ⟨2, by ring⟩
  have hL4 : ∀ μ : Fin 3, 4 ≤ scExt m μ := by
    intro μ
    have := hL μ
    omega
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hkey := hall (scExt m) 3 (by omega) hm hL4 hdvd₀ hdvdm (trivialU _)
    (scField 3 (3 * m) suTwoWitness)
    (by
      intro y hy x _ b hb
      exact scField_axial (L := scExt m) (e := 3) (n := 3 * m) suTwoWitness
        ⟨m, by ring⟩ y hy x b hb)
    (by
      intro c
      exact scField_kerQ (L := scExt m) (e := 3) (n := 3 * m) suTwoWitness (hdvdm 2) c)
  exact scale_body_fails (L := scExt m) (e := 3) (n := 3 * m) (by omega) (by omega)
    hdvdm hdvd₀ hγc hw hkey

/-- **`CoarseCurlPoincareScaled r` IS FALSE, at EVERY decay rate `r`** — including the `r = 5` that
`coarseCurlPoincare_scaled_ell0_one` proves at the fibre `ell₀ = 1`. No permitted decay in the
coarsening ratio rescues the primitive, because the failure is not about the constant. -/
theorem not_coarseCurlPoincareScaled (r : ℕ) : ¬ CoarseCurlPoincareScaled r := fun h =>
  not_coarseCurlPoincareAtScale 2 le_rfl (scaled_imp_atScale h 2 le_rfl)

/-- The witness's coarse average is nonzero and its covariant coarse-curl energy vanishes — the
single pair of facts both refutations consume, recorded on its own. -/
theorem witness_summary {e n : ℕ} (he : 2 ≤ e) (h2e : 2 * e ≤ n)
    {L : PeriodicLatticeExtent} (hdvdn : ∀ μ : Fin 3, n ∣ (L μ + 1))
    (hdvd₀ : ∀ μ : Fin 3, e ∣ (L μ + 1)) {w : SuTwo} (hw : w ≠ 0) :
    0 < covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))
          (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))
      ∧ coarseCurlEnergyCov hdvd₀ (coarseBackground (trivialU L) e)
          (lineCoarseRestrictCovLM (trivialU L) e (scField e n w)) = 0 :=
  ⟨scField_Q_norm_pos (L := L) he h2e hdvdn hw,
   scField_coarseCurlEnergy_zero (L := L) (lt_of_lt_of_le two_pos he) hdvd₀ w⟩

/-! ## §8 — THE SURVIVING FIBRE `ell₀ = 1`: its decay exponent is at least `2`

`CoarseCurlPoincare` §7 proves the `ell₀ = 1` fibre at `r = 5` (constant `1/(56·m⁵)`, on the
`hstrict` slice), and §4's square wave refutes `r = 0`, leaving the compiled bracket `1 ≤ r ≤ 5`.
§7 above kills the FULL primitive at every `r`, so that bracket is void for
`CoarseCurlPoincareScaled`; but it remains the live question for the fibre that survives, which is
the statement `CoarseCurlPoincareFibreOne` below (the body of `CoarseCurlPoincareScaled` with
`ell₀ := 1`, verbatim — `fibreOne_of_scaled` records that it IS a specialization).

This section tightens the bracket to `2 ≤ r ≤ 5` by refuting `r = 1`.

**Why the square wave cannot do it.** §4's profile has amplitude `1` and three jumps, so its energy
ratio is `2p/6 = Θ(m)`: it satisfies the `r = 1` form (with `γc = 6`, in fact the `r = 2` form) and
only refutes `r = 0`. Forcing `r ≥ 2` needs a profile with amplitude `Θ(m)` built from `Θ(m)` UNIT
steps — a periodic SAWTOOTH. Its ratio is `Θ(m²)`.

`sawN q` is the sawtooth of period `8q+8`: it rises `0 → 2q+2` on `[0, 2q+2]`, falls to `−(2q+2)` on
`[2q+2, 6q+6]`, and returns to `0` on `[6q+6, 8q+8]`. Three facts drive everything:

* `sawN_step`: every one-step difference is `±1`, so the squared-difference sum is EXACTLY the
  period `8q+8` (no estimate);
* `sum_sawN`: the profile sums to `0` over a period — proved from the antisymmetry
  `sawN q a = −sawN q b` for `a + b = 8q+8` via `Finset.sum_range_reflect`, so no
  arithmetic-progression summation is needed anywhere;
* `sum_sawN_sq_ge`: the squared sum is `≥ (q+1)³` — a subset bound on `Ico (q+1) (2q+2)`, where the
  profile is `≥ q+1`; again no closed form is needed.

The scope asymmetry is inherited unchanged from the previous lane and is stated, not repaired: the
`r = 5` upper end (`coarseCurlPoincare_scaled_ell0_one`) carries `hstrict` (more than one `m`-block
per direction), while the refutations of `r = 0` and `r = 1` live on a single-block torus. -/

/-! ### §8a — the sawtooth profile on `ℕ` -/

/-- The sawtooth of period `8q+8`, as a function of the raw index. -/
noncomputable def sawN (q k : ℕ) : ℝ :=
  if k ≤ 2 * q + 2 then (k : ℝ)
  else if k ≤ 6 * q + 6 then 4 * (q : ℝ) + 4 - (k : ℝ)
  else (k : ℝ) - (8 * (q : ℝ) + 8)

theorem sawN_lo (q k : ℕ) (h : k ≤ 2 * q + 2) : sawN q k = (k : ℝ) := by
  unfold sawN; rw [if_pos h]

theorem sawN_mid (q k : ℕ) (h1 : ¬ (k ≤ 2 * q + 2)) (h2 : k ≤ 6 * q + 6) :
    sawN q k = 4 * (q : ℝ) + 4 - (k : ℝ) := by
  unfold sawN; rw [if_neg h1, if_pos h2]

theorem sawN_hi (q k : ℕ) (h1 : ¬ (k ≤ 2 * q + 2)) (h2 : ¬ (k ≤ 6 * q + 6)) :
    sawN q k = (k : ℝ) - (8 * (q : ℝ) + 8) := by
  unfold sawN; rw [if_neg h1, if_neg h2]

theorem sawN_zero (q : ℕ) : sawN q 0 = 0 := by
  rw [sawN_lo q 0 (by omega)]
  norm_num

theorem sawN_period (q : ℕ) : sawN q (8 * q + 8) = 0 := by
  rw [sawN_hi q (8 * q + 8) (by omega) (by omega)]
  push_cast
  ring

/-- **ANTISYMMETRY about the period**: `sawN q a = −sawN q b` whenever `a + b = 8q+8`. Proved by a
five-way split with no summation; this is what makes `sum_sawN` free. -/
theorem sawN_antisymm (q a b : ℕ) (hab : a + b = 8 * q + 8) : sawN q a = - sawN q b := by
  rcases (by omega : a ≤ 2 * q + 2 ∨ (2 * q + 2 < a ∧ a ≤ 6 * q + 6) ∨ 6 * q + 6 < a) with h | h | h
  · rcases (by omega : b ≤ 6 * q + 6 ∨ 6 * q + 6 < b) with hb | hb
    · have ha : a = 2 * q + 2 := by omega
      have hb' : b = 6 * q + 6 := by omega
      subst ha; subst hb'
      rw [sawN_lo q _ (by omega), sawN_mid q _ (by omega) (by omega)]
      push_cast; ring
    · rw [sawN_lo q a h, sawN_hi q b (by omega) (by omega)]
      have hR : (a : ℝ) + (b : ℝ) = 8 * (q : ℝ) + 8 := by exact_mod_cast hab
      linarith
  · rcases (by omega : b ≤ 2 * q + 2 ∨ 2 * q + 2 < b) with hb | hb
    · have ha : a = 6 * q + 6 := by omega
      have hb' : b = 2 * q + 2 := by omega
      subst ha; subst hb'
      rw [sawN_mid q _ (by omega) (by omega), sawN_lo q _ (by omega)]
      push_cast; ring
    · rw [sawN_mid q a (by omega) h.2, sawN_mid q b (by omega) (by omega)]
      have hR : (a : ℝ) + (b : ℝ) = 8 * (q : ℝ) + 8 := by exact_mod_cast hab
      linarith
  · rw [sawN_hi q a (by omega) (by omega), sawN_lo q b (by omega)]
    have hR : (a : ℝ) + (b : ℝ) = 8 * (q : ℝ) + 8 := by exact_mod_cast hab
    linarith

/-- **The sawtooth sums to zero over a period** — from antisymmetry and
`Finset.sum_range_reflect`. -/
theorem sum_sawN (q : ℕ) : ∑ k ∈ Finset.range (8 * q + 8), sawN q k = 0 := by
  have hrefl : ∑ j ∈ Finset.range (8 * q + 8), sawN q (8 * q + 8 - 1 - j)
      = ∑ j ∈ Finset.range (8 * q + 8), sawN q j :=
    Finset.sum_range_reflect (fun k => sawN q k) (8 * q + 8)
  have hpt : ∀ j ∈ Finset.range (8 * q + 8),
      sawN q (8 * q + 8 - 1 - j) = - sawN q (j + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact sawN_antisymm q _ _ (by omega)
  rw [Finset.sum_congr rfl hpt, Finset.sum_neg_distrib] at hrefl
  have hshift : ∑ j ∈ Finset.range (8 * q + 8), sawN q (j + 1)
      = ∑ j ∈ Finset.range (8 * q + 8), sawN q j := by
    have h1 := Finset.sum_range_succ' (fun i => sawN q i) (8 * q + 8)
    have h2 := Finset.sum_range_succ (fun i => sawN q i) (8 * q + 8)
    rw [sawN_zero] at h1
    rw [sawN_period] at h2
    simp only [add_zero] at h1 h2
    rw [h2] at h1
    exact h1.symm
  rw [hshift] at hrefl
  linarith

/-- **Every one-step difference of the sawtooth is `±1`** — so the squared-difference sum is exactly
the period. Five cases, no estimates. -/
theorem sawN_step (q v : ℕ) (hv : v < 8 * q + 7) : (sawN q (v + 1) - sawN q v) ^ 2 = 1 := by
  rcases (by omega : v + 1 ≤ 2 * q + 2 ∨ v = 2 * q + 2 ∨ (2 * q + 2 < v ∧ v + 1 ≤ 6 * q + 6)
      ∨ v = 6 * q + 6 ∨ 6 * q + 6 < v) with h | h | h | h | h
  · rw [sawN_lo q _ (by omega), sawN_lo q _ (by omega)]; push_cast; ring
  · subst h
    rw [sawN_mid q _ (by omega) (by omega), sawN_lo q _ (by omega)]; push_cast; ring
  · rw [sawN_mid q _ (by omega) (by omega), sawN_mid q _ (by omega) (by omega)]
    push_cast; ring
  · subst h
    rw [sawN_hi q _ (by omega) (by omega), sawN_mid q _ (by omega) (by omega)]
    push_cast; ring
  · rw [sawN_hi q _ (by omega) (by omega), sawN_hi q _ (by omega) (by omega)]
    push_cast; ring

/-- **The squared sum is at least `(q+1)³`** — a subset bound on `Ico (q+1) (2q+2)`, where the
sawtooth equals its index and is therefore `≥ q+1`. -/
theorem sum_sawN_sq_ge (q : ℕ) :
    ((q : ℝ) + 1) ^ 3 ≤ ∑ k ∈ Finset.range (8 * q + 8), (sawN q k) ^ 2 := by
  have hsub : Finset.Ico (q + 1) (2 * q + 2) ⊆ Finset.range (8 * q + 8) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  have hle : ∑ k ∈ Finset.Ico (q + 1) (2 * q + 2), (sawN q k) ^ 2
      ≤ ∑ k ∈ Finset.range (8 * q + 8), (sawN q k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
  have hcard : (Finset.Ico (q + 1) (2 * q + 2)).card = q + 1 := by
    rw [Nat.card_Ico]; omega
  have hb : ∀ k ∈ Finset.Ico (q + 1) (2 * q + 2), ((q : ℝ) + 1) ^ 2 ≤ (sawN q k) ^ 2 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [sawN_lo q k (by omega)]
    have hqk : ((q : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast (by omega : q + 1 ≤ k)
    have hq0 : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
    nlinarith [hqk, hq0]
  have hcnt := Finset.card_nsmul_le_sum (Finset.Ico (q + 1) (2 * q + 2))
    (fun k => (sawN q k) ^ 2) (((q : ℝ) + 1) ^ 2) hb
  rw [hcard, nsmul_eq_mul] at hcnt
  have hpow : ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ 2 = ((q : ℝ) + 1) ^ 3 := by ring
  push_cast at hcnt
  linarith [hcnt, hle, hpow]

/-! ### §8b — the sawtooth on the lattice -/

/-- The single-block witness torus of side `8q+8`. -/
def sawExt (q : ℕ) : PeriodicLatticeExtent := fun _ => 8 * q + 7

theorem sawExt_apply (q : ℕ) (μ : Fin 3) : sawExt q μ = 8 * q + 7 := rfl

/-- The sawtooth at the type the lattice hands us. -/
noncomputable def sawProfile (q : ℕ) (ν : Fin 3) : Fin (sawExt q ν + 1) → ℝ := fun t => sawN q t.val

theorem sawProfile_zero (q : ℕ) (ν : Fin 3) :
    sawProfile q ν (0 : Fin (sawExt q ν + 1)) = 0 := sawN_zero q

theorem sum_sawProfile (q : ℕ) (ν : Fin 3) : ∑ t, sawProfile q ν t = 0 := by
  rw [show (∑ t : Fin (sawExt q ν + 1), sawProfile q ν t)
      = ∑ k ∈ Finset.range (sawExt q ν + 1), sawN q k from
    Fin.sum_univ_eq_sum_range (fun k => sawN q k) (sawExt q ν + 1),
    show sawExt q ν + 1 = 8 * q + 8 from by unfold sawExt; omega]
  exact sum_sawN q

theorem sum_sawProfile_sq_ge (q : ℕ) (ν : Fin 3) :
    ((q : ℝ) + 1) ^ 3 ≤ ∑ t, (sawProfile q ν t) ^ 2 := by
  rw [show (∑ t : Fin (sawExt q ν + 1), (sawProfile q ν t) ^ 2)
      = ∑ k ∈ Finset.range (sawExt q ν + 1), (sawN q k) ^ 2 from
    Fin.sum_univ_eq_sum_range (fun k => (sawN q k) ^ 2) (sawExt q ν + 1),
    show sawExt q ν + 1 = 8 * q + 8 from by unfold sawExt; omega]
  exact sum_sawN_sq_ge q

theorem sawProfile_diff_sq (q : ℕ) (ν : Fin 3) (t : Fin (sawExt q ν + 1)) :
    (sawProfile q ν (t + 1) - sawProfile q ν t) ^ 2 = 1 := by
  by_cases htl : t = Fin.last (sawExt q ν)
  · have hv : t.val = 8 * q + 7 := by rw [htl, Fin.val_last]; rfl
    have h1 : ((t + 1) : Fin (sawExt q ν + 1)).val = 0 := by
      rw [Fin.val_add_one, if_pos htl]
    change (sawN q ((t + 1) : Fin (sawExt q ν + 1)).val - sawN q t.val) ^ 2 = 1
    rw [h1, hv, sawN_zero, sawN_hi q _ (by omega) (by omega)]
    push_cast
    ring
  · have h1 : ((t + 1) : Fin (sawExt q ν + 1)).val = t.val + 1 := by
      rw [Fin.val_add_one, if_neg htl]
    have hlt : t.val < 8 * q + 7 := by
      have h2 : t.val < sawExt q ν + 1 := t.isLt
      have h3 : t.val ≠ 8 * q + 7 := fun hc => htl (Fin.ext (by rw [Fin.val_last]; exact hc))
      have h4 : sawExt q ν = 8 * q + 7 := rfl
      omega
    change (sawN q ((t + 1) : Fin (sawExt q ν + 1)).val - sawN q t.val) ^ 2 = 1
    rw [h1]
    exact sawN_step q t.val hlt

theorem sum_sawProfile_diff (q : ℕ) (ν : Fin 3) :
    ∑ t, (sawProfile q ν (t + 1) - sawProfile q ν t) ^ 2 = 8 * (q : ℝ) + 8 := by
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => sawProfile_diff_sq q ν t)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : sawExt q ν + 1 = 8 * q + 8 := by unfold sawExt; omega
  rw [this]
  push_cast
  ring

/-! ### §8c — the witness field, its two gauge clauses, and the exact energy identity -/

/-- **The sawtooth witness**: the field `sawProfile q (x₁) • w` on direction-`2` bonds. -/
noncomputable def SAW (q : ℕ) (w : SuTwo) : Bond (sawExt q) → SuTwo :=
  coordField 2 1 (sawProfile q 1) w

theorem saw_coarse_site_zero (q : ℕ) {y : PeriodicLatticeSite (sawExt q)}
    (hy : y ∈ CoarseLattice (sawExt q) (8 * q + 8)) (μ : Fin 3) : (y μ).val = 0 := by
  have h : (y μ).val % (8 * q + 8) = 0 := mem_CoarseLattice.mp hy μ
  have hlt : (y μ).val < sawExt q μ + 1 := (y μ).isLt
  have hE : sawExt q μ = 8 * q + 7 := rfl
  rw [Nat.mod_eq_of_lt (by omega)] at h
  exact h

theorem saw_block_univ (q : ℕ) {y : PeriodicLatticeSite (sawExt q)}
    (hy : y ∈ CoarseLattice (sawExt q) (8 * q + 8)) :
    blockOf y (8 * q + 8) = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => ?_
  rw [mem_blockOf]
  intro μ
  have h0 := saw_coarse_site_zero q hy μ
  have hlt : (x μ).val < sawExt q μ + 1 := (x μ).isLt
  have hE : sawExt q μ = 8 * q + 7 := rfl
  omega

/-- **The sawtooth witness is in the axial gauge at level `8q+8`.** -/
theorem SAW_axial (q : ℕ) (w : SuTwo) {y : PeriodicLatticeSite (sawExt q)}
    (hy : y ∈ CoarseLattice (sawExt q) (8 * q + 8)) (x : PeriodicLatticeSite (sawExt q))
    (b : Bond (sawExt q)) (hb : b ∈ staircasePath y x) : SAW q w b = 0 := by
  classical
  unfold SAW
  rw [coordField_apply]
  by_cases hd : b.2 = 2
  · rw [if_pos hd]
    rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
    rcases hb with (hb | hb) | hb
    · rw [mem_axisSegment] at hb
      have h1 : b.1 1 = y 1 := hb.2.1 1 (by decide)
      have hy1 : y 1 = (0 : Fin (sawExt q 1 + 1)) := Fin.ext (saw_coarse_site_zero q hy 1)
      rw [h1, hy1, sawProfile_zero, zero_smul]
    · rw [mem_axisSegment] at hb
      exact absurd (hb.1.symm.trans hd) (by decide)
    · rw [mem_axisSegment] at hb
      exact absurd (hb.1.symm.trans hd) (by decide)
  · rw [if_neg hd]

/-- **The sawtooth witness is in `ker Q_{8q+8}(1)`** — the profile sums to zero over the block. -/
theorem SAW_kerQ (q : ℕ) (w : SuTwo) (c : CoarseBond (sawExt q) (8 * q + 8)) :
    lineCoarseRestrictCov (trivialU (sawExt q)) (8 * q + 8) (SAW q w) c = 0 := by
  classical
  unfold SAW
  rw [Q_coordField (8 * q + 8) 2 1 (by decide) (sawProfile q 1) w c]
  have hsum : ∑ x ∈ blockOf c.1.1 (8 * q + 8), sawProfile q 1 (x 1) = 0 := by
    rw [saw_block_univ q c.1.2]
    rw [show (∑ x ∈ (Finset.univ : Finset (PeriodicLatticeSite (sawExt q))),
          sawProfile q 1 (x 1))
        = ∑ x : PeriodicLatticeSite (sawExt q), sawProfile q 1 (x 1) from rfl,
      sum_site_coord 1 (sawProfile q 1), sum_sawProfile q 1, mul_zero]
  by_cases hc : c.2 = 2
  · rw [if_pos hc, hsum, mul_zero, mul_zero, zero_smul]
  · rw [if_neg hc, mul_zero, zero_smul]

/-- **THE EXACT ENERGY IDENTITY**, division-free and numeral-free: bond energy times the
squared-difference sum equals curl energy times the squared sum. -/
theorem saw_energies (q : ℕ) (w : SuTwo) :
    bondEnergy (SAW q w) * (∑ t, (sawProfile q 1 (t + 1) - sawProfile q 1 t) ^ 2)
      = plaqEnergy (flatCurlValue (SAW q w)) * (∑ t, (sawProfile q 1 t) ^ 2) := by
  unfold SAW
  rw [bondEnergy_coordField, plaqEnergy_coordField 2 1 (by decide),
    sum_site_coord 1 (fun t => (sawProfile q 1 t) ^ 2),
    sum_site_coord 1 (fun t => (sawProfile q 1 (t + 1) - sawProfile q 1 t) ^ 2)]
  ring

theorem saw_bond_pos (q : ℕ) {w : SuTwo} (hw : w ≠ 0) : 0 < bondEnergy (SAW q w) := by
  unfold SAW
  rw [bondEnergy_coordField, sum_site_coord 1 (fun t => (sawProfile q 1 t) ^ 2)]
  have hC := card_other_coords_pos (L := sawExt q) 1
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hS : (0 : ℝ) < ∑ t, (sawProfile q 1 t) ^ 2 := by
    have := sum_sawProfile_sq_ge q 1
    have hq : (0 : ℝ) < ((q : ℝ) + 1) ^ 3 := by positivity
    linarith
  positivity

/-- **THE ARITHMETIC CORE**: any positive `γ` with `γ·bondEnergy ≤ plaqEnergy` on the sawtooth obeys
`γ·(q+1)³ ≤ 8q+8`, i.e. `γ = O(m⁻²)` at side `m = 8q+8`. -/
theorem saw_forces_bound {γ : ℝ} (q : ℕ) (hγ : 0 < γ) {w : SuTwo} (hw : w ≠ 0)
    (h : γ * bondEnergy (SAW q w) ≤ plaqEnergy (flatCurlValue (SAW q w))) :
    γ * ((q : ℝ) + 1) ^ 3 ≤ 8 * (q : ℝ) + 8 := by
  set b := bondEnergy (SAW q w) with hbdef
  set P := plaqEnergy (flatCurlValue (SAW q w)) with hPdef
  set S := ∑ t, (sawProfile q 1 t) ^ 2 with hSdef
  have hid : b * (8 * (q : ℝ) + 8) = P * S := by
    rw [hbdef, hPdef, hSdef, ← sum_sawProfile_diff q 1]
    exact saw_energies q w
  have hbpos : 0 < b := saw_bond_pos q hw
  have hSge : ((q : ℝ) + 1) ^ 3 ≤ S := sum_sawProfile_sq_ge q 1
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hSge
  -- `γ·b·S ≤ P·S = b·(8q+8)`, then divide by `b > 0`
  have hstep : γ * b * S ≤ b * (8 * (q : ℝ) + 8) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_right h (le_of_lt hSpos)
  have hgS : γ * S ≤ 8 * (q : ℝ) + 8 := by
    refine le_of_mul_le_mul_right ?_ hbpos
    linarith [hstep]
  nlinarith [hgS, hSge, hγ]

/-! ### §8d — the fibre statement and its exponent bracket -/

/-- **The `ell₀ = 1` FIBRE of `CoarseCurlPoincareScaled r`** — its body with `ell₀ := 1`, verbatim.
This is the statement that SURVIVES §7's refutation of the full primitive. -/
def CoarseCurlPoincareFibreOne (r : ℕ) : Prop :=
  ∃ γc : ℝ, 0 < γc ∧
    ∀ (L : PeriodicLatticeExtent) (m : ℕ), 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      ∀ (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)),
        (∀ μ : Fin 3, (1 * m) ∣ (L μ + 1)) →
        ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (1 * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (1 * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (1 * m), lineCoarseRestrictCov U (1 * m) B c = 0) →
          (γc / (m : ℝ) ^ r) * covCoarseBondInner (lineCoarseRestrictCovLM U 1 B)
              (lineCoarseRestrictCovLM U 1 B)
            ≤ coarseCurlEnergyCov hdvd1 (coarseBackground U 1)
                (lineCoarseRestrictCovLM U 1 B)

/-- The fibre statement IS a specialization of the full scaled primitive (`ell₀ := 1`), so any
refutation of the fibre refutes the full primitive too. -/
theorem fibreOne_of_scaled {r : ℕ} (h : CoarseCurlPoincareScaled r) :
    CoarseCurlPoincareFibreOne r := by
  obtain ⟨γc, hγc, hall⟩ := h
  exact ⟨γc, hγc, fun L m hm hL hdvd1 hdvdm U B hadm hker =>
    hall L 1 m one_pos hm hL hdvd1 hdvdm U B hadm hker⟩

/-- **`CoarseCurlPoincareFibreOne 1` IS FALSE** — the sawtooth forces `γc·(q+1)² ≤ 8` at side
`m = 8q+8`, so no constant survives `q → ∞`. Together with `coarseCurlPoincare_scaled_ell0_one`
(which gives `r = 5` on the `hstrict` slice) the compiled bracket for the surviving fibre is
`2 ≤ r ≤ 5`, tightening the previous lane's `1 ≤ r ≤ 5`. -/
theorem not_coarseCurlPoincareFibreOne_one : ¬ CoarseCurlPoincareFibreOne 1 := by
  classical
  rintro ⟨γc, hγc, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (64 / γc)
  set q := n with hqdef
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (sawExt q μ + 1) := fun _ => one_dvd _
  have hdvdm : ∀ μ : Fin 3, ((1 * (8 * q + 8) : ℕ)) ∣ (sawExt q μ + 1) := by
    intro μ
    rw [one_mul, show sawExt q μ + 1 = 8 * q + 8 from by unfold sawExt; omega]
  have hL4 : ∀ μ : Fin 3, 4 ≤ sawExt q μ := by
    intro μ
    change 4 ≤ 8 * q + 7
    omega
  have hkey := hall (sawExt q) (8 * q + 8) (by omega) hL4 hdvd1 hdvdm
    (trivialU _) (SAW q suTwoWitness)
    (by
      rw [one_mul]
      exact fun y hy x _ b hb => SAW_axial q suTwoWitness hy x b hb)
    (by
      rw [one_mul]
      exact fun c => SAW_kerQ q suTwoWitness c)
  rw [covCoarseBondInner_one_eq_bondEnergy, coarseCurlEnergyCov_trivialU,
    coarseCurlEnergySuTwo_one_eq_plaqEnergy, curl_trivialU_eq_flat] at hkey
  have hmpos : (0 : ℝ) < ((8 * q + 8 : ℕ) : ℝ) ^ 1 := by
    have : (0 : ℝ) < ((8 * q + 8 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    positivity
  have hgpos : 0 < γc / ((8 * q + 8 : ℕ) : ℝ) ^ 1 := div_pos hγc hmpos
  have hb := saw_forces_bound q hgpos hw hkey
  -- `γc/(8q+8) · (q+1)³ ≤ 8q+8`, i.e. `γc·(q+1)² ≤ 64`
  have hcast : ((8 * q + 8 : ℕ) : ℝ) = 8 * (q : ℝ) + 8 := by push_cast; ring
  rw [pow_one, hcast] at hb
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hkey2 : γc * ((q : ℝ) + 1) ≤ 64 := by
    have h8 : (0 : ℝ) < 8 * (q : ℝ) + 8 := by linarith
    have hmul : γc * ((q : ℝ) + 1) ^ 3 ≤ (8 * (q : ℝ) + 8) * (8 * (q : ℝ) + 8) :=
      (div_le_iff₀ h8).mp (by
        calc γc * ((q : ℝ) + 1) ^ 3 / (8 * (q : ℝ) + 8)
            = γc / (8 * (q : ℝ) + 8) * ((q : ℝ) + 1) ^ 3 := by ring
          _ ≤ 8 * (q : ℝ) + 8 := hb)
    have hsq : (0 : ℝ) < ((q : ℝ) + 1) ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hsq
    have e1 : γc * ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ 2 = γc * ((q : ℝ) + 1) ^ 3 := by ring
    have e2 : (8 * (q : ℝ) + 8) * (8 * (q : ℝ) + 8) = 64 * ((q : ℝ) + 1) ^ 2 := by ring
    linarith [hmul, e1, e2]
  have hqn : (64 : ℝ) / γc < (q : ℝ) := hn
  rw [div_lt_iff₀ hγc] at hqn
  linarith [hkey2, hqn, hγc]

/-! ## §A — AXIOM AUDIT -/

#print axioms psiSc
#print axioms psiSc_nonneg
#print axioms psiSc_eq_zero_of_coord1
#print axioms scField
#print axioms scField_dir_ne
#print axioms scField_eq_zero_of_coord1
#print axioms coord1_mod_coarseShift
#print axioms psiSc_coarseShift
#print axioms psiSc_coarseShift_n
#print axioms scBlockSum
#print axioms scField_lineSum
#print axioms scField_Q
#print axioms scQ
#print axioms scQ_eq_LM
#print axioms scQ_dir2
#print axioms scQ_dir_ne
#print axioms scField_axial
#print axioms scField_kerQ
#print axioms scBlockSum_coarseShift
#print axioms scField_coarseCurl_zero
#print axioms scField_coarseCurlEnergy_zero
#print axioms scOrigin
#print axioms scOrigin_val
#print axioms scStar
#print axioms scStar_val
#print axioms scOrigin_mem_coarse
#print axioms scBlockSum_origin_neg
#print axioms scField_Q_norm_pos
#print axioms scale_body_fails
#print axioms scExt
#print axioms scExt_add_one
#print axioms not_coarseCurlPoincareAtScale
#print axioms not_coarseCurlPoincareScaled
#print axioms witness_summary

#print axioms sawN
#print axioms sawN_lo
#print axioms sawN_mid
#print axioms sawN_hi
#print axioms sawN_zero
#print axioms sawN_period
#print axioms sawN_antisymm
#print axioms sum_sawN
#print axioms sawN_step
#print axioms sum_sawN_sq_ge
#print axioms sawExt
#print axioms sawExt_apply
#print axioms sawProfile
#print axioms sawProfile_zero
#print axioms sum_sawProfile
#print axioms sum_sawProfile_sq_ge
#print axioms sawProfile_diff_sq
#print axioms sum_sawProfile_diff
#print axioms SAW
#print axioms saw_coarse_site_zero
#print axioms saw_block_univ
#print axioms SAW_axial
#print axioms SAW_kerQ
#print axioms saw_energies
#print axioms saw_bond_pos
#print axioms saw_forces_bound
#print axioms CoarseCurlPoincareFibreOne
#print axioms fibreOne_of_scaled
#print axioms not_coarseCurlPoincareFibreOne_one

end AdalyFormal.Balaban.CoarseCurlScaleTwo
