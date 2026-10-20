/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockedGaugeCore

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Ū` — witnesses and CONTROLS, both directions

`BlockedGaugeCore.blockedGauge_gauge` proves gauge covariance from the `LogExpAd` hypotheses. This
module is the adversarial half: it establishes what that theorem does and does NOT certify.

## §A — the MUST-FIRE control (the degenerate inhabitant)

`trivialLogExp` satisfies every `LogExpAd` law and makes `Ū(c) = U(c)` exactly: the blocked field
forgets the block. So **an inhabitant of `Averaging.GaugeCovariant` is worth nothing on its own** —
`gaugeCovariant_blockedGauge` instantiated at `trivialLogExp` is a true theorem about a map that
does no averaging at all. Any future consumer must pin the `LogExpAd` it uses.

## §B — degeneracy at small `ell`

At `ell = 1` the block is a single site and `Ū(c) = U(c)` for EVERY `LogExpAd` with `log 1 = 0`,
`exp 0 = 1`. This is the `ell ∈ {0,1}` degenerate point flagged in the campaign's own trap list,
proved rather than assumed. At `ell = 0` the coarse bond is empty and `Ū(c) = exp(0) = 1`.

## §C — a non-degenerate witness

The abelian instance `G = Multiplicative ℚ`, `𝔤 = ℚ`, with `log`/`exp` the EXACT group isomorphism
(the same honest abelian instantiation `Averaging.lean` uses, and exactly Bałaban's formula for
abelian `G` — no approximation), and `Ad = id`. **Limitation stated as a fact: `Ad = id` here, so
the conjugation content of `log_conj`/`exp_ad` is not exercised by this witness.** §E supplies a
witness with `Ad ≠ id`.
-/

namespace AdalyFormal.Balaban.BlockedGauge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf inBlock mem_blockOf CoarseLattice
  mem_CoarseLattice)

variable {L : PeriodicLatticeExtent}

/-! ## §0. The quantifier domain of `gaugeCovariant_blockedGauge` is INHABITED -/

/-- The all-zero site is always a coarse-lattice point, so the subtype indexing
`gaugeCovariant_blockedGauge`'s coarse configurations is nonempty and the theorem is not vacuous
by an empty index. -/
theorem coarseLattice_nonempty (ell : ℕ) (L : PeriodicLatticeExtent) :
    (fun _ : Fin 3 => (0 : Fin (L _ + 1))) ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  simp

theorem coarseBond_subtype_nonempty (ell : ℕ) (L : PeriodicLatticeExtent) (ν : Fin 3) :
    Nonempty {c : CoarseBond L // c.2 = ν ∧ c.1 ∈ CoarseLattice L ell} :=
  ⟨⟨((fun _ => (0 : Fin (L _ + 1))), ν), rfl, coarseLattice_nonempty ell L⟩⟩

/-! ## §A. THE MUST-FIRE CONTROL — `LogExpAd` has a degenerate inhabitant -/

/-- Every `LogExpAd` law holds for `log = 0`, `exp = 1`, `Ad = 0`. -/
def trivialLogExp (G 𝔤 : Type*) [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤] : LogExpAd G 𝔤 where
  log := fun _ => 0
  exp := fun _ => 1
  ad := fun _ => 0
  log_conj := by intro g X; simp
  exp_ad := by intro g A; simp

/-- **The control fires.** With the degenerate pair, `Ū(c) = U(c)` — the "blocked" field is just
the fine holonomy along the coarse bond, no averaging whatsoever. -/
theorem blockedGauge_trivialLogExp {G : Type*} [Group G] (ell : ℕ)
    (U : PeriodicLinkConfiguration G L) (c : CoarseBond L) :
    blockedGauge (trivialLogExp G ℚ) ell U c
      = periodicPathHolonomy U c.1 (straightSeg c.2 ell) := by
  simp [blockedGauge, trivialLogExp]

/-- …and it is still gauge-covariant. So covariance ALONE certifies nothing about `Ū` being a
genuine average. -/
theorem trivial_still_covariant {G : Type*} [Group G] {ell : ℕ} (hell : 0 < ell)
    (γ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L) (c : CoarseBond L)
    (hdvd : ell ∣ (L c.2 + 1)) (hc : c.1 ∈ CoarseLattice L ell) :
    blockedGauge (trivialLogExp G ℚ) ell (periodicGaugeTransform γ U) c
      = coarseGaugeTransform ell γ (blockedGauge (trivialLogExp G ℚ) ell U) c :=
  blockedGauge_gauge (trivialLogExp G ℚ) hell γ U c hdvd hc

/-! ## §B. Trivial configuration and small-`ell` degeneracy -/

/-- The trivial fine configuration has trivial holonomy along every path. -/
theorem holonomy_trivialU {G : Type*} [Group G] (y : PeriodicLatticeSite L)
    (s : List (Fin 3 × Bool)) :
    periodicPathHolonomy (fun _ => (1 : G)) y s = 1 := by
  induction s generalizing y with
  | nil => rfl
  | cons st rest ih =>
      simp only [periodicPathHolonomy]
      rw [ih (periodicLatticeStep y st)]
      by_cases hb : st.2 = true <;> simp [hb]

/-- Walking a path and then its reverse inverts the holonomy. -/
theorem holonomy_revSteps {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)) :
    periodicPathHolonomy U (periodicPathEndpoint y s) (revSteps s)
      = (periodicPathHolonomy U y s)⁻¹ := by
  induction s generalizing y with
  | nil => simp [periodicPathHolonomy, periodicPathEndpoint]
  | cons st rest ih =>
      rw [revSteps_cons]
      simp only [periodicPathEndpoint]
      rw [holonomy_append, ih (periodicLatticeStep y st), endpoint_revSteps]
      simp only [periodicPathHolonomy, mul_inv_rev, mul_one]
      congr 1
      by_cases hb : st.2 = true
      · have hstep : periodicLatticeStep (periodicLatticeStep y st) (st.1, false) = y := by
          simpa [hb] using step_flip y st
        simp only [hb, Bool.not_true, Bool.false_eq_true, if_false, if_true, hstep]
      · have hb' : st.2 = false := by simpa using hb
        have hstep : periodicLatticeStep (periodicLatticeStep y st) (st.1, !st.2) = y :=
          step_flip y st
        simp only [hb', Bool.not_false, if_true, Bool.false_eq_true, if_false, inv_inv]

/-- **`Ū(1) = 1`.** The blocked field of the trivial configuration is trivial, for ANY `LogExpAd`
normalised by `log 1 = 0`, `exp 0 = 1`. This is the reduction the `U = 1` tower law
(`ThirdLevelArrows.tower_law`) needs: the covariant object restricts correctly. -/
theorem blockedGauge_trivialU {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : LogExpAd G 𝔤) (hlog1 : P.log 1 = 0) (hexp0 : P.exp 0 = 1) (ell : ℕ)
    (c : CoarseBond L) :
    blockedGauge P ell (fun _ => (1 : G)) c = 1 := by
  have hinner : ∀ x : PeriodicLatticeSite L, innerAvg P ell (fun _ => (1 : G)) c x = 0 := by
    intro x
    simp only [innerAvg]
    refine Finset.sum_eq_zero (fun Γ _ => ?_)
    rw [Finset.sum_eq_zero (fun Γ' _ => ?_), smul_zero]
    rw [holonomy_trivialU, hlog1, smul_zero]
  simp only [blockedGauge]
  rw [Finset.sum_congr rfl (fun x _ => by rw [hinner x, smul_zero]), Finset.sum_const_zero,
    hexp0, holonomy_trivialU, one_mul]

/-- **Degenerate point `ell = 1`, proved.** A one-site block gives `Ū(c) = U(c)`: the (0.4) loop
degenerates to the bond `c` followed by its own reverse, whose holonomy is `1`. -/
theorem blockedGauge_ell_one {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : LogExpAd G 𝔤) (hlog1 : P.log 1 = 0) (hexp0 : P.exp 0 = 1)
    (U : PeriodicLinkConfiguration G L) (c : CoarseBond L) :
    blockedGauge P 1 U c = periodicPathHolonomy U c.1 (straightSeg c.2 1) := by
  have hblock : ∀ x ∈ blockOf c.1 1, x = c.1 := by
    intro x hx
    funext μ
    have := mem_blockOf.mp hx μ
    exact (Fin.ext (by omega)).symm
  have hfam : ∀ y : PeriodicLatticeSite L, contourFamily y y = {([] : List (Fin 3 × Bool))} := by
    intro y
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · simp only [contourFamily, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨1, by simp [contourSteps]⟩
    · intro s hs
      simp only [contourFamily, Finset.mem_image, Finset.mem_univ, true_and] at hs
      obtain ⟨π, rfl⟩ := hs
      simp [contourSteps]
  have hloop : periodicPathHolonomy U c.1 (loopSteps 1 c.2 [] []) = 1 := by
    have hshape : loopSteps 1 c.2 [] [] = straightSeg c.2 1 ++ revSteps (straightSeg c.2 1) := by
      simp [loopSteps, revSteps]
    rw [hshape, holonomy_append, holonomy_revSteps, mul_inv_cancel]
  have hinner : ∀ x ∈ blockOf c.1 1, innerAvg P 1 U c x = 0 := by
    intro x hx
    have hxc : x = c.1 := hblock x hx
    subst hxc
    have hx2 : shiftBy c.1 c.2 1 = cPlus 1 c := rfl
    simp only [innerAvg, hfam, Finset.sum_singleton, hx2, hfam]
    rw [hloop, hlog1, smul_zero, smul_zero]
  simp only [blockedGauge]
  rw [Finset.sum_congr rfl (fun x hx => by rw [hinner x hx, smul_zero]), Finset.sum_const_zero,
    hexp0, one_mul]

/-! ## §C. The abelian witness — every `LogExpAd` law discharged, EXACTLY -/

/-- `G = Multiplicative ℚ`, `𝔤 = ℚ`, `log`/`exp` the exact group isomorphism, `Ad = id`.
For abelian `G` this is Bałaban's (0.4) verbatim, with no approximation: an abelian one-parameter
group's logarithm IS the isomorphism, not a linearisation of it. -/
def ratLogExp : LogExpAd (Multiplicative ℚ) ℚ where
  log := Multiplicative.toAdd
  exp := Multiplicative.ofAdd
  ad := fun _ => LinearMap.id
  log_conj := by
    intro g X
    have : g * X * g⁻¹ = X := by
      rw [mul_comm g X, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    rfl
  exp_ad := by
    intro g A
    have : g * Multiplicative.ofAdd A * g⁻¹ = Multiplicative.ofAdd A := by
      rw [mul_comm g _, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    rfl

@[simp] theorem ratLogExp_log_one : ratLogExp.log 1 = 0 := rfl
@[simp] theorem ratLogExp_exp_zero : ratLogExp.exp 0 = 1 := rfl

/-! ## §D. Net winding, constant configurations, and NON-CONSTANCY of `Ū` -/

/-- Signed step count of a path: `+1` per forward bond, `−1` per backward bond. -/
def netSteps : List (Fin 3 × Bool) → ℤ
  | [] => 0
  | st :: rest => (if st.2 then (1 : ℤ) else -1) + netSteps rest

@[simp] theorem netSteps_nil : netSteps [] = 0 := rfl

theorem netSteps_append (s t : List (Fin 3 × Bool)) :
    netSteps (s ++ t) = netSteps s + netSteps t := by
  induction s with
  | nil => simp [netSteps]
  | cons st rest ih => simp only [List.cons_append, netSteps, ih]; ring

theorem netSteps_revSteps (s : List (Fin 3 × Bool)) : netSteps (revSteps s) = - netSteps s := by
  induction s with
  | nil => simp
  | cons st rest ih =>
      rw [revSteps_cons, netSteps_append, ih]
      simp only [netSteps]
      by_cases hb : st.2 = true <;> simp [hb]

theorem netSteps_replicate (μ : Fin 3) (k : ℕ) :
    netSteps (List.replicate k (μ, true)) = (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ]; simp only [netSteps, ih]; push_cast; ring

theorem netSteps_straightSeg (ν : Fin 3) (m : ℕ) : netSteps (straightSeg ν m) = (m : ℤ) :=
  netSteps_replicate ν m

theorem netSteps_contourSteps (π : Equiv.Perm (Fin 3)) (y x : PeriodicLatticeSite L) :
    netSteps (contourSteps π y x)
      = ((x (π 0)).val - (y (π 0)).val : ℕ) + (((x (π 1)).val - (y (π 1)).val : ℕ) : ℤ)
        + (((x (π 2)).val - (y (π 2)).val : ℕ) : ℤ) := by
  simp only [contourSteps, netSteps_append, netSteps_replicate]
  ring

/-- Holonomy of a CONSTANT configuration is a power of the constant, determined by the net winding
— valid in any group, since powers of one element commute. -/
theorem holonomy_const {G : Type*} [Group G] (g : G) (y : PeriodicLatticeSite L)
    (s : List (Fin 3 × Bool)) :
    periodicPathHolonomy (fun _ => g) y s = g ^ (netSteps s) := by
  induction s generalizing y with
  | nil => simp [periodicPathHolonomy]
  | cons st rest ih =>
      simp only [periodicPathHolonomy, netSteps]
      rw [ih (periodicLatticeStep y st), zpow_add g]
      by_cases hb : st.2 = true <;> simp [hb]

/-- **The `ν`-coordinate displacement is preserved by the block shift**, given the standing torus
compatibility. The wrap-around case (`c_- + ell = L ν + 1`) is genuinely different and is handled
separately; this is the fact that makes the (0.4) loop have zero net winding. -/
theorem shiftBy_disp_eq {ell : ℕ} (hell : 0 < ell) {ν : Fin 3} (hdvd : ell ∣ (L ν + 1))
    {cm x : PeriodicLatticeSite L} (hc : cm ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf cm ell) (μ : Fin 3) :
    ((shiftBy x ν ell) μ).val - ((shiftBy cm ν ell) μ).val = (x μ).val - (cm μ).val := by
  by_cases hμ : μ = ν
  · subst hμ
    rw [shiftBy_val, shiftBy_val]
    have hblk := mem_blockOf.mp hx μ
    have hcm : ell ∣ (cm μ).val := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hc μ)
    have haN : (cm μ).val < L μ + 1 := (cm μ).isLt
    have hbN : (x μ).val < L μ + 1 := (x μ).isLt
    have hstep1 : (cm μ).val + ell ≤ L μ + 1 := dvd_gap hell hdvd hcm haN
    rcases eq_or_lt_of_le hstep1 with heq | hlt
    · rw [heq, Nat.mod_self]
      have : (x μ).val + ell - (L μ + 1) = (x μ).val - (cm μ).val := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have hstep2 : ((cm μ).val + ell) + ell ≤ L μ + 1 :=
        dvd_gap hell hdvd (Dvd.dvd.add hcm dvd_rfl) hlt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [shiftBy_apply_of_ne cm hμ ell, shiftBy_apply_of_ne x hμ ell]

/-- **Every (0.4) loop has zero net winding.** -/
theorem netSteps_loop_zero {ell : ℕ} (hell : 0 < ell) (c : CoarseBond L)
    (hdvd : ell ∣ (L c.2 + 1)) (hc : c.1 ∈ CoarseLattice L ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf c.1 ell)
    {Γ Γ' : List (Fin 3 × Bool)} (hΓ : Γ ∈ contourFamily c.1 x)
    (hΓ' : Γ' ∈ contourFamily (cPlus ell c) (shiftBy x c.2 ell)) :
    netSteps (loopSteps ell c.2 Γ Γ') = 0 := by
  simp only [contourFamily, Finset.mem_image, Finset.mem_univ, true_and] at hΓ hΓ'
  obtain ⟨π, rfl⟩ := hΓ
  obtain ⟨σ, rfl⟩ := hΓ'
  have hd : ∀ μ : Fin 3,
      ((shiftBy x c.2 ell) μ).val - ((cPlus ell c) μ).val = (x μ).val - (c.1 μ).val := by
    intro μ
    exact shiftBy_disp_eq hell hdvd hc hx μ
  simp only [loopSteps, netSteps_append, netSteps_revSteps, netSteps_straightSeg,
    netSteps_contourSteps, hd]
  have hsum : ∀ π' : Equiv.Perm (Fin 3),
      (((x (π' 0)).val - (c.1 (π' 0)).val : ℕ) : ℤ)
        + (((x (π' 1)).val - (c.1 (π' 1)).val : ℕ) : ℤ)
        + (((x (π' 2)).val - (c.1 (π' 2)).val : ℕ) : ℤ)
      = ∑ μ : Fin 3, (((x μ).val - (c.1 μ).val : ℕ) : ℤ) := by
    intro π'
    have h := Fintype.sum_equiv π'
      (fun i : Fin 3 => (((x (π' i)).val - (c.1 (π' i)).val : ℕ) : ℤ))
      (fun μ : Fin 3 => (((x μ).val - (c.1 μ).val : ℕ) : ℤ)) (fun _ => rfl)
    rw [Fin.sum_univ_three] at h
    exact h
  rw [hsum π, hsum σ]
  ring

/-- **`Ū` of a CONSTANT configuration is `g^ell` — i.e. exactly `U(c)`.**

Every (0.4) loop closes with zero net winding, so the exponent vanishes and the blocked field is
the bare coarse holonomy. Two consequences, both recorded as facts:
* `Ū` is NON-CONSTANT in `U` (combine with `blockedGauge_trivialU`): a genuine dependence.
* the constant family does **not** separate `Ū` from the degenerate `trivialLogExp` pair — on
  constants both give `U(c)`. Any separation must use a non-flat configuration. -/
theorem blockedGauge_const {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : LogExpAd G 𝔤) (hlog1 : P.log 1 = 0) (hexp0 : P.exp 0 = 1)
    {ell : ℕ} (hell : 0 < ell) (g : G) (c : CoarseBond L)
    (hdvd : ell ∣ (L c.2 + 1)) (hc : c.1 ∈ CoarseLattice L ell) :
    blockedGauge P ell (fun _ => g) c = g ^ (ell : ℤ) := by
  have hinner : ∀ x ∈ blockOf c.1 ell, innerAvg P ell (fun _ => g) c x = 0 := by
    intro x hx
    simp only [innerAvg]
    refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
    rw [Finset.sum_eq_zero (fun Γ' hΓ' => ?_), smul_zero]
    rw [holonomy_const, netSteps_loop_zero hell c hdvd hc hx hΓ hΓ', zpow_zero, hlog1, smul_zero]
  simp only [blockedGauge]
  rw [Finset.sum_congr rfl (fun x hx => by rw [hinner x hx, smul_zero]), Finset.sum_const_zero,
    hexp0, one_mul, holonomy_const, netSteps_straightSeg]

/-- **`Ū` is not constant in `U`.** Concretely on the `4`-sites-per-direction torus with `ell = 2`:
`Ū(1) = 1` but `Ū(const (ofAdd 1)) = ofAdd 2 ≠ 1`. -/
theorem blockedGauge_nonconstant :
    ∃ (Lw : PeriodicLatticeExtent) (c : CoarseBond Lw)
      (U₁ U₂ : PeriodicLinkConfiguration (Multiplicative ℚ) Lw),
      blockedGauge ratLogExp 2 U₁ c ≠ blockedGauge ratLogExp 2 U₂ c := by
  refine ⟨fun _ => 3, ((fun _ => (0 : Fin 4)), 0), (fun _ => 1),
    (fun _ => Multiplicative.ofAdd (1 : ℚ)), ?_⟩
  rw [blockedGauge_trivialU ratLogExp rfl rfl,
    blockedGauge_const ratLogExp rfl rfl (by decide) _ _ (by decide)
      (coarseLattice_nonempty 2 _)]
  intro h
  rw [show (((2 : ℕ) : ℤ)) = 2 from rfl, zpow_two] at h
  have h2 : (0 : ℚ) = 1 + 1 := by
    have h3 := congrArg Multiplicative.toAdd h
    simpa using h3
  norm_num at h2

end AdalyFormal.Balaban.BlockedGauge
