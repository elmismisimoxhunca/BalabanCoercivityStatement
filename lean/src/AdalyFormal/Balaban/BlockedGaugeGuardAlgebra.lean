/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockedGaugeGuardSU2

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# RETYPING `(0.4)` INTO `su(2)` — the algebra carrier, not the ambient matrix algebra

`SuTwoLogExpCore.su2LogExp` has `𝔤 := M₂(ℂ)`, the AMBIENT matrix algebra. The grade-3 prosecution
recorded that as residual `[BLOCKED-SU2-ALGEBRA]`: *"no type in `blockedGauge` forces its exponent
to inhabit a source-defined `su(2)` subtype"*, even though `SuTwoLogExpTorus` already proves
`su2Log` is traceless and anti-Hermitian.

This module closes the RETYPING half. `su2Alg` is the `ℚ`-submodule of traceless anti-Hermitian
`2×2` complex matrices — the standard `su(2)` — and `su2AlgLogExp : LogExpAd SU2 ↥su2Alg` is the
same log/exp/ad triple with the exponent's TYPE narrowed to it. `su2AlgFaithful` lifts it to the
guarded interface, and `su2AlgGuarded` re-runs the pinned witness over the narrowed carrier, so the
narrowing costs nothing: the value is still `torus E ≠ 1`.

## What is NOT closed here, stated precisely

`su2Exp` still carries `SuTwoLogExpCore`'s totalising guard (`if exp A ∈ SU(2) then … else 1`), and
retyping the DOMAIN of `exp` does not by itself discharge it. Discharging it means proving

> `∀ A : M₂(ℂ), trace A = 0 → Aᴴ = −A → NormedSpace.exp A ∈ specialUnitaryGroup (Fin 2) ℂ`

The unitarity half of that is proved here (`exp_antiHerm_mem_unitary`); the `det = 1` half is NOT
proved, and §4 below states exactly where the attempt stops and what is missing. Note the direction
of the residual risk, unchanged from `SuTwoLogExpCore`: a spuriously triggered guard can only make
`exp` MORE trivial, so it can never manufacture a separation — it could only suppress one.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.BlockedGauge
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice)

/-! ## §1. `su(2)` as a `ℚ`-submodule of `M₂(ℂ)` -/

/-- **`su(2)`**: the traceless anti-Hermitian `2×2` complex matrices, as a `ℚ`-submodule of the
ambient algebra. (`ℚ` because that is the scalar ring `LogExpAd` requires — every weight in (0.4)
is rational. It is a `ℝ`-subspace too; only the `ℚ`-structure is used.) -/
def su2Alg : Submodule ℚ M2 where
  carrier := {A : M2 | Matrix.trace A = 0 ∧ Aᴴ = -A}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.trace_add, ha1, hb1, add_zero]
    · rw [Matrix.conjTranspose_add, ha2, hb2, neg_add]
  zero_mem' := by
    refine ⟨Matrix.trace_zero _ _, ?_⟩
    simp
  smul_mem' := by
    rintro q a ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.trace_smul, h1, smul_zero]
    · rw [Matrix.conjTranspose_rat_smul, h2, smul_neg]

@[simp] theorem mem_su2Alg {A : M2} : A ∈ su2Alg ↔ Matrix.trace A = 0 ∧ Aᴴ = -A := Iff.rfl

/-- `su2Log` really lands in `su(2)` — both halves are already theorems of `SuTwoLogExpTorus`. -/
theorem su2Log_mem_su2Alg (g : SU2) : su2Log g ∈ su2Alg :=
  ⟨su2Log_traceless g, su2Log_antiHermitian g⟩

/-- Conjugation preserves `su(2)`. -/
theorem adMap_mem_su2Alg (g : SU2) {A : M2} (hA : A ∈ su2Alg) : adMap g A ∈ su2Alg := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨?_, ?_⟩
  · rw [adMap_apply, Matrix.trace_mul_comm ((g : M2) * A) ((g : M2)ᴴ), ← Matrix.mul_assoc,
      star_mul_self, Matrix.one_mul, h1]
  · rw [adMap_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2]
    simp

/-- `Ad g` restricted to `su(2)`, as a `ℚ`-linear endomorphism of the carrier. -/
noncomputable def adAlg (g : SU2) : ↥su2Alg →ₗ[ℚ] ↥su2Alg where
  toFun A := ⟨adMap g (A : M2), adMap_mem_su2Alg g A.2⟩
  map_add' A B := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact map_add (adMap g) _ _
  map_smul' q A := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul]
    exact map_smul (adMap g) q _

@[simp] theorem adAlg_coe (g : SU2) (A : ↥su2Alg) : ((adAlg g A : ↥su2Alg) : M2) = adMap g A := rfl

/-! ## §2. The `LogExpAd` instance over the narrowed carrier -/

/-- **`LogExpAd SU2 su(2)`** — the same log/exp/ad triple as `su2LogExp`, with the exponent typed
into the algebra instead of the ambient `M₂(ℂ)`. -/
noncomputable def su2AlgLogExp : LogExpAd SU2 ↥su2Alg where
  log g := ⟨su2Log g, su2Log_mem_su2Alg g⟩
  exp A := su2Exp (A : M2)
  ad := adAlg
  log_conj g X := by
    apply Subtype.ext
    exact su2_log_conj g X
  exp_ad g A := by
    rw [adAlg_coe]
    exact su2_exp_ad g (A : M2)

@[simp] theorem su2AlgLogExp_log_coe (g : SU2) :
    ((su2AlgLogExp.log g : ↥su2Alg) : M2) = su2Log g := rfl

@[simp] theorem su2AlgLogExp_exp (A : ↥su2Alg) : su2AlgLogExp.exp A = su2Exp (A : M2) := rfl

/-- **The narrowed pair, lifted to the guarded interface.** Same branch domain as `su2Faithful`. -/
noncomputable def su2AlgFaithful : FaithfulLogExpAd SU2 ↥su2Alg where
  toLogExpAd := su2AlgLogExp
  dom := conjPrincipal
  one_mem := conjPrincipal_one
  dom_conj := fun k g hg => conjPrincipal_conj hg k
  exp_log := fun _ hg => su2_exp_log_of_conjPrincipal hg
  log_one := by
    apply Subtype.ext
    exact su2Log_one
  exp_zero := su2Exp_zero
  witness := torus (1 : ℝ)
  witness_mem := ⟨1, 1, by norm_num, by linarith [Real.pi_gt_three], by group⟩
  witness_ne_one := torus_one_ne_one

/-- Retyping does not resurrect the hostile pairs: they are still excluded, now at the narrowed
carrier. -/
theorem su2Alg_no_faithful_trivial (F : FaithfulLogExpAd SU2 ↥su2Alg) :
    F.toLogExpAd ≠ trivialLogExp SU2 ↥su2Alg :=
  no_faithful_trivial F

/-! ## §3. The pinned witness survives the retyping -/

/-- The coerced inner average over the narrowed carrier IS the ambient one. -/
theorem coe_innerAvg_su2Alg {L : PeriodicLatticeExtent} (ell : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) (c : CoarseBond L) (x : PeriodicLatticeSite L) :
    ((innerAvg su2AlgLogExp ell U c x : ↥su2Alg) : M2) = innerAvg su2LogExp ell U c x := by
  simp only [innerAvg, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  rfl

theorem coe_exponent_su2Alg {L : PeriodicLatticeExtent} (ell : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) (c : CoarseBond L) :
    ((∑ x ∈ blockOf c.1 ell, (((ell : ℚ)) ^ 3)⁻¹ • innerAvg su2AlgLogExp ell U c x : ↥su2Alg)
        : M2)
      = ∑ x ∈ blockOf c.1 ell, (((ell : ℚ)) ^ 3)⁻¹ • innerAvg su2LogExp ell U c x := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [SetLike.val_smul, coe_innerAvg_su2Alg]

/-- The narrowed instance produces the SAME group element as the ambient one, bond by bond: the
exponent is the same matrix, only its type changed. -/
theorem blockedGauge_su2Alg_eq {L : PeriodicLatticeExtent} (ell : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) (c : CoarseBond L) :
    blockedGauge su2AlgLogExp ell U c = blockedGauge su2LogExp ell U c := by
  simp only [blockedGauge, su2AlgLogExp_exp, su2LogExp_exp, coe_exponent_su2Alg]

/-- **The guarded instance over `su(2)`.** Every field discharged, at the pinned configuration. -/
noncomputable def su2AlgGuarded : GuardedBlocking SU2 ↥su2Alg witLw where
  P := su2AlgFaithful
  ell := 2
  two_le_ell := le_refl 2
  ell_dvd := by decide
  U := sU
  c := wc
  base_coarse := w_coarse
  loops_dom := fun _ hx _ hΓ _ hΓ' => sU_loop_mem_conjPrincipal hx hΓ hΓ'

/-- **The narrowing costs nothing.** -/
theorem su2AlgGuarded_value : su2AlgGuarded.value = torus ((wE : ℚ) : ℝ) := by
  rw [GuardedBlocking.value_eq]
  change blockedGauge su2AlgLogExp 2 sU wc = _
  rw [blockedGauge_su2Alg_eq]
  exact su2_blockedGauge_eq_torus

theorem su2AlgGuarded_value_ne_one : su2AlgGuarded.value ≠ 1 := by
  rw [GuardedBlocking.value_eq]
  change blockedGauge su2AlgLogExp 2 sU wc ≠ 1
  rw [blockedGauge_su2Alg_eq]
  exact su2_blockedGauge_ne_one

/-! ## §4. Toward discharging the totalising guard: the UNITARITY half

`su2Exp` is `NormedSpace.exp` guarded by membership in `SU(2)`. For `A ∈ su(2)` the unitarity half
of that membership is a theorem: `Aᴴ = −A` gives `(exp A)ᴴ = exp(Aᴴ) = exp(−A) = (exp A)⁻¹`. -/

/-- **`exp` of an anti-Hermitian matrix is unitary.** -/
theorem exp_antiHerm_mem_unitary {A : M2} (h : Aᴴ = -A) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hct : (NormedSpace.exp A)ᴴ = NormedSpace.exp (-A) := by
    rw [← h]
    exact (Matrix.exp_conjTranspose A).symm
  have hcomm : Commute A (-A) := (Commute.refl A).neg_right
  have hmul : NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
    rw [← Matrix.exp_add_of_commute A (-A) hcomm, add_neg_cancel, NormedSpace.exp_zero]
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, hct]
  exact hmul

/-- The same statement for members of the carrier. -/
theorem exp_su2Alg_mem_unitary (A : ↥su2Alg) :
    NormedSpace.exp (A : M2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  exp_antiHerm_mem_unitary A.2.2

end AdalyFormal.Balaban.SuTwoLogExp
