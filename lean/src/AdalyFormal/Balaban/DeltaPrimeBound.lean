/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.GammaRecursion
import AdalyFormal.Balaban.LemmaAssemblyNormalized
import AdalyFormal.Balaban.GeneralUHodgeDrift
import AdalyFormal.Balaban.WeightedQNorm

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `DeltaPrimeBound.lean` — bounding `δ`, the one quantity CMP99b p.419 defers

Lane record: `compute/delta_bound/PROGRESS.md`; repair record `compute/delta_repair/PROGRESS.md`.

**⚠ THIS MODULE IS AN ISLAND — NOTHING IMPORTS IT.** Measured at repair time
(`grep -rln "^import.*DeltaPrimeBound" formal/ --include=*.lean` → no hits): **zero importers**. The
only other file that names it is `KappaBound.lean`, which cites it in eight docstring passages and
*deliberately declines to import it* (its own "Import note (LAW-4)": this file had no `.olean` and a
concurrent lane was compiling it). So every theorem below is proved and none is consumed, and §12's
demonstration of fit is instantiated nowhere. Stated here for the same reason
`CStarLevelProbe.lean` states it: an unconsumed proof is not part of the composed result, however
clean its axioms are.

**⚠ WHAT THE TWO PROSECUTIONS CONVICTED, AND WHERE EACH IS ANSWERED.** Two de-correlated families
(Claude, `compute/delta_prosecution/VERDICT.md`; Kimi K3, `compute/kimi_delta/VERDICT.md`) cleared
the mathematics of §2–§5, §7, §8 and convicted the framing:

* the §12 wrapper targets a socket the tree had already proved witness-less — **§12a** now proves
  that deadness *in this file* rather than leaving it to a citation;
* `q = 1/2` was a bare literal — **§9** now derives it from `WeightedQNorm`;
* the headline margin `≈2.76×` belongs to `Δ′_source`, not to `Δ′_π` — **§9a** pins both, separately;
* `κ` was unpinned, and the demo instances take `κ = 1` — `KappaBound.lean` has since landed
  `κ ≤ 16√3 = √768 ≈ 27.71` (**conditionally**: its block-Poincaré input `hblock` is open — §9b
  reads that at the source and does not launder it), and **§9b** composes it: at `κ = √768` the
  criterion **FAILS** at the tree's own regularity radius. §9b also carries the control that stops
  that being over-read — at `Jsup = 24·normAlpha` the criterion fails **already at `κ = 1`**, so the
  failure there is not `κ`'s doing; what `κ` costs is a factor `495`–`496` in `δ`.

**THE TARGET.** `RecursiveBridge.bridge_from_piExtended_normalized_threeTen` consumes
`hpi : ∀ x, |⟨x, Δ′_π x⟩| ≤ δ‖x‖²` on (3.120)'s indefinite correction and returns a coercivity
constant that iterates as `γ_{k+1} = (γ_k − δ)/q²`. CMP99b p.419 says of `Δ′_π` only *"The quadratic
form `Δ′_π` is a small perturbation of `Δ`. Later we will write bounds for this form"* — and those
bounds are not in the papers this campaign holds.

**THE OBJECT, FROM THE SOURCE PAGE, NOT FROM A DESCRIPTION.**
`corpus/pages/CMP99b_p419.md#eq-3-120` (400 dpi render `corpus/renders/CMP99b_p419-31.png`,
`render_sha256: b23f5197bcd55b03423163a5dc1ccbae7a8e28d7e8ad384ee11e0a9aad83f51d`) prints

```
⟨A, Δ_π A⟩ = ⟨A, Δ A⟩ − ⟨ i[(G'RD*A)(b₋), A(b)]
                          − i[A(b), R_b(G'RD*A)(b₊)]
                          − i[(G'RD*A)(b₋), (DG'RD*A)(b)] , J ⟩
           = ⟨A, Δ A⟩ − ⟨A, Δ′_π A⟩
```

with `J = D*η⁻²Im ∂U` (p.419, four lines above (3.118)). Writing `λ := G'RD*A` for the gauge
parameter that projects `A` onto the slice `{RD*A = 0}`, `⟨A,Δ′_πA⟩` is the bond sum of the three
commutators paired against `J`. That is `deltaPrimePiForm` below, transcribed term by term.

**WHAT IS NEW HERE, AND WHAT IS NOT.** The tree already carries a bound on the *other* `Δ′` — the
(3.10)-level `Δ′_source` sitting inside `Δ = D*D + Δ′`
(`LemmaAssemblyNormalized.abs_deltaPrimeQuadFormNormalizedTransported_le`). **That is a different
object**: `piExtendedMap Delta DeltaPrimePi = Delta − DeltaPrimePi` subtracts `Δ′_π` from a `Δ` that
already contains `Δ′_source`. §5 below adds the missing companion — a pure bond-energy bound on
`Δ′_source` — but §2–§4, the `Δ′_π` bound, are this lane's mathematics.

**THE STRUCTURE OF THE ANSWER.** `Δ′_π` is *bilinear in `(λ, A)` and LINEAR IN `J`*. So the bound
factorizes into exactly two inputs and nothing else:

* `Jsup` — the sup-norm of the curvature current `J` (small with the background's regularity: §6);
* `κ` — the operator bound `‖G'RD*A‖_{ℓ²(sites)} ≤ κ‖A‖_{ℓ²(bonds)}` of the gauge projector's
  Green's-function leg.

and the answer is `δ = Jsup·κ·(28 + 48κ)` (§4, `deltaPiConst`), with **no lattice-volume factor**
— the point that has to be checked, and is (`§4`'s proof runs Cauchy–Schwarz at the bond sum, never
a triangle inequality over sites).

**THE `HolonomyDomination` TRANSFER QUESTION, ANSWERED.** `HolonomyDomination.lean` refutes, at
every positive threshold, that `IsRegularHolonomy U Mα₀` forces `0 ≤ dstarDQuadForm U A +
deltaPrimeQuadFormTransported U A`. §7 shows why that refutation cannot transfer to the question
here, *constructively*: `dstarD_zero_bondEnergy_pos` exhibits a background and a field with
`dstarDQuadForm = 0 < bondEnergy`, and `no_reverse_bound_at_constant_field` turns that into the
statement that no positive `δ` can bridge boundedness to domination; so a two-sided `|Δ′| ≤ δ·bondEnergy` bound — however small `δ` —
never implies domination. Domination needs a REVERSE inequality `bondEnergy ≲ dstarDQuadForm` that
is false at a constant field, and it is that reverse inequality, not the boundedness, that
`HolonomyDomination` kills. The two statements are logically independent, and §2–§4 prove one of
them.
-/

namespace AdalyFormal.Balaban.DeltaPrimeBound

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy siteEnergy_nonneg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.LemmaAssembly (abs_im_trace_comm_le frobNorm_coe_suTwo
  frobNorm_holonomy_sub_one_le frobSq_imHolonomy_le)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular norm_RMap sqrt_two_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime (imHolonomy)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `i[X,Y]` and the single-commutator trace bound

`X, Y : SuTwo` are skew-Hermitian, so `i[X,Y]` is Hermitian — the same reason
`DeltaPrime.commutatorMatrixSum` carries its `Complex.I •`, and the reason the pairing against the
Hermitian `J` under a real trace is the right one. -/

/-- `i[X,Y]`, at the ambient-matrix level. -/
noncomputable def iComm (X Y : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I •
    ((X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ)
      - (Y : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ))

/-- **The single-commutator pairing bound**: `|Re tr(i[X,Y]·M)| ≤ 8‖X‖‖Y‖·‖M‖_F`.

`8 = 4 · (√2)²`: `LemmaAssembly.abs_im_trace_comm_le`'s `4` (REUSED, LAW-19 — not re-derived) times
the two `frobNorm (X : Matrix) = √2‖X‖` conversions. -/
theorem abs_re_trace_iComm_le (X Y : SuTwo) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    |(Matrix.trace (iComm X Y * M)).re| ≤ 8 * ‖X‖ * ‖Y‖ * frobNorm M := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set x : Matrix (Fin 2) (Fin 2) ℂ := (X : Matrix (Fin 2) (Fin 2) ℂ) with hx
  set y : Matrix (Fin 2) (Fin 2) ℂ := (Y : Matrix (Fin 2) (Fin 2) ℂ) with hy
  have hre : (Matrix.trace (iComm X Y * M)).re = -(Matrix.trace ((x * y - y * x) * M)).im := by
    unfold iComm
    rw [← hx, ← hy, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre, abs_neg]
  refine (abs_im_trace_comm_le x y M).trans ?_
  have hfx : frobNorm x = Real.sqrt 2 * ‖X‖ := frobNorm_coe_suTwo X
  have hfy : frobNorm y = Real.sqrt 2 * ‖Y‖ := frobNorm_coe_suTwo Y
  rw [hfx, hfy]
  have h : 4 * (Real.sqrt 2 * ‖X‖) * (Real.sqrt 2 * ‖Y‖) * frobNorm M
      = 4 * (Real.sqrt 2 * Real.sqrt 2) * ‖X‖ * ‖Y‖ * frobNorm M := by ring
  rw [h, hs2]
  linarith

#print axioms abs_re_trace_iComm_le

/-! ## §2 — (3.120)'s form, transcribed

`λ` is carried as a SITE function, exactly as `G'RD*A` is: `G'` inverts a site-level operator on
`N(Q')` and `R D*` maps bond fields to site fields. `(Dλ)(b)` is the tree's own
`CovariantOperators.gradValueCovariant` (`RMap (U b) (λ(b₊)) − λ(b₋)`), reused rather than rebuilt. -/

/-- (3.120)'s per-bond integrand, before pairing with `J`:
`i[λ(b₋),A(b)] − i[A(b),R_bλ(b₊)] − i[λ(b₋),(Dλ)(b)]`. -/
noncomputable def piBondValue
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (b : Bond L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  iComm (lam b.1) (A b)
    - iComm (A b) (RMap (U b) (lam (periodicLatticeShift b.1 b.2)))
    - iComm (lam b.1) (gradValueCovariant U lam b)

/-- **`⟨A, Δ′_π A⟩`, CMP99b (3.120)** — the bond sum of `piBondValue` paired against the curvature
current `J`. `lam` is `G'RD*A`; `J` is `D*η⁻²Im ∂U`. Both are carried as data, so this definition
commits to (3.120)'s ALGEBRA without committing to a construction of `G'` or of `η`. -/
noncomputable def deltaPrimePiForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) : ℝ :=
  ∑ b : Bond L, (Matrix.trace (piBondValue U lam A b * J b)).re

/-- **`Δ′_π` VANISHES ON THE GAUGE SLICE** — the load-bearing structural fact
(`compute/cstar_deltak_c_su2/DELTA_PI_ADJUDICATED.md`, main-loop image read): every term of (3.120)
carries a `G'RD*A` factor, so at `λ = 0` (which is what `RD*A = 0` gives) the form is identically
zero. Proved here from this file's own definition, not asserted. -/
theorem deltaPrimePiForm_eq_zero_of_lam_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A : Bond L → SuTwo) :
    deltaPrimePiForm U J (fun _ => 0) A = 0 := by
  unfold deltaPrimePiForm
  refine Finset.sum_eq_zero (fun b _ => ?_)
  have hgrad : gradValueCovariant U (fun _ : PeriodicLatticeSite L => (0 : SuTwo)) b = 0 := by
    unfold gradValueCovariant; simp
  have hpb : piBondValue U (fun _ : PeriodicLatticeSite L => (0 : SuTwo)) A b = 0 := by
    unfold piBondValue iComm
    rw [hgrad]
    simp
  rw [hpb]
  simp

#print axioms deltaPrimePiForm_eq_zero_of_lam_zero

/-! ## §3 — the two incidence identities and the covariant-gradient energy bound

`Bond L = PeriodicLatticeSite L × Fin 3` (`AdmissibleSubspace.Bond`, `ClayStatement`), so a site
function evaluated at a bond's TAIL is counted once per direction, `3` times in `d = 3`. The HEAD
count is the same by the shift bijection `periodicLatticeShiftEquiv` (REUSED — the same equiv
`LemmaAssemblyNormalized.sum_nbr1_sq_eq` uses). -/

/-- `∑_b ‖λ(b₋)‖² = 3·siteEnergy λ` — EXACT, at every extent. -/
theorem sum_lam_tail_sq_eq (lam : PeriodicLatticeSite L → SuTwo) :
    ∑ b : Bond L, ‖lam b.1‖ ^ 2 = 3 * siteEnergy lam := by
  rw [Fintype.sum_prod_type (f := fun b : PeriodicLatticeSite L × Fin 3 => ‖lam b.1‖ ^ 2)]
  unfold siteEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Finset.sum_const]

/-- `∑_b ‖λ(b₊)‖² = 3·siteEnergy λ` — same count after the shift bijection. -/
theorem sum_lam_head_sq_eq (lam : PeriodicLatticeSite L → SuTwo) :
    ∑ b : Bond L, ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2 = 3 * siteEnergy lam := by
  rw [Fintype.sum_prod_type
    (f := fun b : PeriodicLatticeSite L × Fin 3 => ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2)]
  rw [Finset.sum_comm]
  have hone : ∀ μ : Fin 3,
      (∑ x : PeriodicLatticeSite L, ‖lam (periodicLatticeShift x μ)‖ ^ 2) = siteEnergy lam := by
    intro μ
    exact Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) μ) (fun y => ‖lam y‖ ^ 2)
  rw [Finset.sum_congr rfl (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin 3))) => hone μ)]
  simp [Finset.sum_const]

/-- **The covariant gradient's energy**: `bondEnergy (D_Uλ) ≤ 12·siteEnergy λ`. `RMap` is an
isometry (`AlphaAnalyticity.norm_RMap`, REUSED), so each bond term is `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²` on
values whose tail/head sums are `3·siteEnergy` each. -/
theorem bondEnergy_gradValueCovariant_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) :
    bondEnergy (gradValueCovariant U lam) ≤ 12 * siteEnergy lam := by
  have hpt : ∀ b : Bond L, ‖gradValueCovariant U lam b‖ ^ 2
      ≤ 2 * ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2 + 2 * ‖lam b.1‖ ^ 2 := by
    intro b
    set g : ℝ := ‖gradValueCovariant U lam b‖ with hg
    set p : ℝ := ‖lam (periodicLatticeShift b.1 b.2)‖ with hp
    set q : ℝ := ‖lam b.1‖ with hq
    have htri : g ≤ p + q := by
      have hR : ‖RMap (U b) (lam (periodicLatticeShift b.1 b.2))‖ = p := by
        rw [hp]; exact norm_RMap _ _
      have h := norm_sub_le (RMap (U b) (lam (periodicLatticeShift b.1 b.2))) (lam b.1)
      rw [hR, ← hq] at h
      exact h
    have hg0 : 0 ≤ g := norm_nonneg _
    nlinarith [htri, hg0, sq_nonneg (p - q)]
  calc bondEnergy (gradValueCovariant U lam)
      = ∑ b : Bond L, ‖gradValueCovariant U lam b‖ ^ 2 := rfl
    _ ≤ ∑ b : Bond L, (2 * ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2 + 2 * ‖lam b.1‖ ^ 2) :=
        Finset.sum_le_sum (fun b _ => hpt b)
    _ = 12 * siteEnergy lam := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_lam_head_sq_eq, sum_lam_tail_sq_eq]
        ring

#print axioms sum_lam_tail_sq_eq
#print axioms sum_lam_head_sq_eq
#print axioms bondEnergy_gradValueCovariant_le

/-! ## §4 — THE BOUND

Three Cauchy–Schwarz applications at the BOND sum, never a triangle inequality over sites — which
is exactly why no lattice-volume factor appears. -/

/-- `√3 ≤ 7/4`. The companion of `AlphaAnalyticity.sqrt_two_le` (REUSED there, minted here for `3`
because no `√3` bound exists in the tree). -/
theorem sqrt_three_le : Real.sqrt 3 ≤ 7 / 4 := by
  calc Real.sqrt 3 ≤ Real.sqrt ((7 / 4 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 7 / 4 := Real.sqrt_sq (by norm_num)

/-- Cauchy–Schwarz on a finite index type, in the `√·√` form. -/
theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  have hcs : (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hnn : 0 ≤ ∑ i, f i * g i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (hg i))
  have hf2 : (0 : ℝ) ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h := Real.sqrt_le_sqrt hcs
  rwa [Real.sqrt_sq hnn, Real.sqrt_mul hf2] at h

/-- **(3.120)'s per-bond term, bounded.** The three commutators are bounded one at a time by §1 and
combined with `|a − b − c| ≤ |a| + |b| + |c|`; `RMap`'s isometry removes the `R_b` from the middle
term. -/
theorem abs_piBond_pairing_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (b : Bond L) :
    |(Matrix.trace (piBondValue U lam A b * J b)).re|
      ≤ 8 * frobNorm (J b) * (‖lam b.1‖ * ‖A b‖
          + ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖
          + ‖lam b.1‖ * ‖gradValueCovariant U lam b‖) := by
  set t1 := (Matrix.trace (iComm (lam b.1) (A b) * J b)).re with ht1
  set t2 := (Matrix.trace
    (iComm (A b) (RMap (U b) (lam (periodicLatticeShift b.1 b.2))) * J b)).re with ht2
  set t3 := (Matrix.trace (iComm (lam b.1) (gradValueCovariant U lam b) * J b)).re with ht3
  have hsplit : (Matrix.trace (piBondValue U lam A b * J b)).re = t1 - t2 - t3 := by
    rw [ht1, ht2, ht3]
    unfold piBondValue
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re,
      Complex.sub_re]
  rw [hsplit]
  have b1 : |t1| ≤ 8 * ‖lam b.1‖ * ‖A b‖ * frobNorm (J b) :=
    abs_re_trace_iComm_le _ _ _
  have b2 : |t2| ≤ 8 * ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖ * frobNorm (J b) := by
    have h := abs_re_trace_iComm_le (A b)
      (RMap (U b) (lam (periodicLatticeShift b.1 b.2))) (J b)
    rwa [norm_RMap] at h
  have b3 : |t3| ≤ 8 * ‖lam b.1‖ * ‖gradValueCovariant U lam b‖ * frobNorm (J b) :=
    abs_re_trace_iComm_le _ _ _
  have hsum : |t1 - t2 - t3| ≤ |t1| + |t2| + |t3| := by
    calc |t1 - t2 - t3| ≤ |t1 - t2| + |t3| := abs_sub _ _
      _ ≤ |t1| + |t2| + |t3| := by linarith [abs_sub t1 t2]
  linarith [hsum, b1, b2, b3]

#print axioms sqrt_three_le
#print axioms sum_mul_le_sqrt_mul_sqrt
#print axioms abs_piBond_pairing_le

/-- **THE RAW ENERGY BOUND** for (3.120)'s form:
`|⟨A,Δ′_πA⟩| ≤ 8·Jsup·(2√(3·siteEnergy λ)·√(bondEnergy A) + 6·siteEnergy λ)`.
No volume factor: the three Cauchy–Schwarz steps are at the bond sum. -/
theorem abs_deltaPrimePiForm_le_energies
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (Jsup : ℝ)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) :
    |deltaPrimePiForm U J lam A|
      ≤ 8 * Jsup * (2 * Real.sqrt (3 * siteEnergy lam) * Real.sqrt (bondEnergy A)
          + 6 * siteEnergy lam) := by
  have hJ0 : 0 ≤ Jsup := le_trans (frobNorm_nonneg _) (hJ (Classical.arbitrary (Bond L)))
  set S := siteEnergy lam with hS
  set E := bondEnergy A with hE
  have hS0 : 0 ≤ S := siteEnergy_nonneg lam
  have hE0 : 0 ≤ E := bondEnergy_nonneg A
  -- (i) termwise
  have hterm : ∀ b : Bond L, |(Matrix.trace (piBondValue U lam A b * J b)).re|
      ≤ 8 * Jsup * (‖lam b.1‖ * ‖A b‖
          + ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖
          + ‖lam b.1‖ * ‖gradValueCovariant U lam b‖) := by
    intro b
    refine (abs_piBond_pairing_le U J lam A b).trans ?_
    have hpos : (0 : ℝ) ≤ ‖lam b.1‖ * ‖A b‖
        + ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖
        + ‖lam b.1‖ * ‖gradValueCovariant U lam b‖ := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hJ b) (by norm_num : (0:ℝ) ≤ 8))
      hpos
    linarith [this]
  have hstep : |deltaPrimePiForm U J lam A|
      ≤ ∑ b : Bond L, 8 * Jsup * (‖lam b.1‖ * ‖A b‖
          + ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖
          + ‖lam b.1‖ * ‖gradValueCovariant U lam b‖) := by
    unfold deltaPrimePiForm
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => hterm b))
  -- (ii) split into three sums
  have hsplit : (∑ b : Bond L, 8 * Jsup * (‖lam b.1‖ * ‖A b‖
        + ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖
        + ‖lam b.1‖ * ‖gradValueCovariant U lam b‖))
      = 8 * Jsup * ((∑ b : Bond L, ‖lam b.1‖ * ‖A b‖)
          + (∑ b : Bond L, ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖)
          + (∑ b : Bond L, ‖lam b.1‖ * ‖gradValueCovariant U lam b‖)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit] at hstep
  refine hstep.trans ?_
  -- (iii) the three Cauchy-Schwarz bounds
  have c1 : (∑ b : Bond L, ‖lam b.1‖ * ‖A b‖) ≤ Real.sqrt (3 * S) * Real.sqrt E := by
    have h := sum_mul_le_sqrt_mul_sqrt (fun b : Bond L => ‖lam b.1‖) (fun b : Bond L => ‖A b‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    rwa [sum_lam_tail_sq_eq, show (∑ b : Bond L, ‖A b‖ ^ 2) = E from rfl] at h
  have c2 : (∑ b : Bond L, ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖)
      ≤ Real.sqrt E * Real.sqrt (3 * S) := by
    have h := sum_mul_le_sqrt_mul_sqrt (fun b : Bond L => ‖A b‖)
      (fun b : Bond L => ‖lam (periodicLatticeShift b.1 b.2)‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    rwa [sum_lam_head_sq_eq, show (∑ b : Bond L, ‖A b‖ ^ 2) = E from rfl] at h
  have c3 : (∑ b : Bond L, ‖lam b.1‖ * ‖gradValueCovariant U lam b‖) ≤ 6 * S := by
    have h := sum_mul_le_sqrt_mul_sqrt (fun b : Bond L => ‖lam b.1‖)
      (fun b : Bond L => ‖gradValueCovariant U lam b‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    rw [sum_lam_tail_sq_eq,
      show (∑ b : Bond L, ‖gradValueCovariant U lam b‖ ^ 2)
        = bondEnergy (gradValueCovariant U lam) from rfl] at h
    have hg : Real.sqrt (bondEnergy (gradValueCovariant U lam)) ≤ Real.sqrt (12 * S) :=
      Real.sqrt_le_sqrt (bondEnergy_gradValueCovariant_le U lam)
    have hprod : Real.sqrt (3 * S) * Real.sqrt (12 * S) = 6 * S := by
      rw [← Real.sqrt_mul (by linarith : (0:ℝ) ≤ 3 * S)]
      rw [show (3 * S) * (12 * S) = (6 * S) ^ 2 by ring]
      exact Real.sqrt_sq (by linarith)
    calc (∑ b : Bond L, ‖lam b.1‖ * ‖gradValueCovariant U lam b‖)
        ≤ Real.sqrt (3 * S) * Real.sqrt (bondEnergy (gradValueCovariant U lam)) := h
      _ ≤ Real.sqrt (3 * S) * Real.sqrt (12 * S) :=
          mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _)
      _ = 6 * S := hprod
  have hcoef : (0 : ℝ) ≤ 8 * Jsup := by positivity
  have hcomm : Real.sqrt E * Real.sqrt (3 * S) = Real.sqrt (3 * S) * Real.sqrt E := by ring
  rw [hcomm] at c2
  have : (∑ b : Bond L, ‖lam b.1‖ * ‖A b‖)
        + (∑ b : Bond L, ‖A b‖ * ‖lam (periodicLatticeShift b.1 b.2)‖)
        + (∑ b : Bond L, ‖lam b.1‖ * ‖gradValueCovariant U lam b‖)
      ≤ 2 * Real.sqrt (3 * S) * Real.sqrt E + 6 * S := by linarith [c1, c2, c3]
  exact mul_le_mul_of_nonneg_left this hcoef

#print axioms abs_deltaPrimePiForm_le_energies

/-- **THE `δ` OF (3.120)**, as a formula in its two and only two inputs: the curvature current's
sup-norm `Jsup` and the gauge-projector Green's-function bound `κ` (`‖G'RD*A‖ ≤ κ‖A‖`).

`Jsup·κ·(28 + 48κ) = 8·Jsup·(2√3·κ + 6κ²)` after `√3 ≤ 7/4`. -/
noncomputable def deltaPiConst (Jsup kappa : ℝ) : ℝ := Jsup * kappa * (28 + 48 * kappa)

/-- **THE BOUND CMP99b p.419 DEFERS.** `|⟨A, Δ′_π A⟩| ≤ δ·bondEnergy A` with
`δ = deltaPiConst Jsup κ`, for every background `U`, every extent `L`, every gauge parameter `λ`
obeying `siteEnergy λ ≤ κ²·bondEnergy A`, and every current `J` with `frobNorm (J b) ≤ Jsup`.

The constant is FREE OF THE LATTICE VOLUME and free of `k`.

**⚠ WHERE THE CONTENT ACTUALLY LIVES — a quantifier note both prosecutions raised, added 2026-07-31.**
In THIS theorem `lam`, `A` and `kappa` are independent universals, so `κ` may be chosen AFTER seeing
the pair: for any `A` with `bondEnergy A > 0` one may take `κ = √(siteEnergy lam / bondEnergy A)`
and `hlam` is free. Read alone, the "for every `A`" here is therefore hollow in the
free-parameter-decides-the-statement sense, and this theorem should not be quoted as an operator
bound.

The substantive statement is `abs_inner_le_of_piForm`, whose `hlam` is `∀ A, siteEnergy (Lam A) ≤
κ²·bondEnergy A` — ONE `κ` uniform in `A`, i.e. a genuine operator bound on `Lam`. On any finite
lattice and any linear `Lam` some finite `κ` exists, so all the content is in `κ`'s SIZE and its
uniformity in the extent and the scale: that is exactly what §9b now prices. -/
theorem abs_deltaPrimePiForm_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (Jsup kappa : ℝ)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) (hk0 : 0 ≤ kappa)
    (hlam : siteEnergy lam ≤ kappa ^ 2 * bondEnergy A) :
    |deltaPrimePiForm U J lam A| ≤ deltaPiConst Jsup kappa * bondEnergy A := by
  have hJ0 : 0 ≤ Jsup := le_trans (frobNorm_nonneg _) (hJ (Classical.arbitrary (Bond L)))
  set S := siteEnergy lam with hS
  set E := bondEnergy A with hE
  have hS0 : 0 ≤ S := siteEnergy_nonneg lam
  have hE0 : 0 ≤ E := bondEnergy_nonneg A
  refine (abs_deltaPrimePiForm_le_energies U J lam A Jsup hJ).trans ?_
  -- `√(3S) ≤ (7/4)·κ·√E`
  have hsq : Real.sqrt (3 * S) ≤ (7 / 4) * (kappa * Real.sqrt E) := by
    have h1 : Real.sqrt (3 * S) = Real.sqrt 3 * Real.sqrt S :=
      Real.sqrt_mul (by norm_num) S
    have h2 : Real.sqrt S ≤ kappa * Real.sqrt E := by
      have := Real.sqrt_le_sqrt hlam
      rwa [Real.sqrt_mul (sq_nonneg kappa), Real.sqrt_sq hk0] at this
    have h3 : Real.sqrt 3 ≤ 7 / 4 := sqrt_three_le
    have h4 : (0 : ℝ) ≤ Real.sqrt S := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ kappa * Real.sqrt E := mul_nonneg hk0 (Real.sqrt_nonneg _)
    calc Real.sqrt (3 * S) = Real.sqrt 3 * Real.sqrt S := h1
      _ ≤ (7 / 4) * (kappa * Real.sqrt E) := by nlinarith [h2, h3, h4, h5, Real.sqrt_nonneg 3]
  have hE2 : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE0
  have hEs0 : (0 : ℝ) ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hfirst : 2 * Real.sqrt (3 * S) * Real.sqrt E ≤ (7 / 2) * kappa * E := by
    nlinarith [hsq, hEs0, hE2]
  have hsecond : 6 * S ≤ 6 * kappa ^ 2 * E := by nlinarith [hlam]
  have hcoef : (0 : ℝ) ≤ 8 * Jsup := by positivity
  calc 8 * Jsup * (2 * Real.sqrt (3 * S) * Real.sqrt E + 6 * S)
      ≤ 8 * Jsup * ((7 / 2) * kappa * E + 6 * kappa ^ 2 * E) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hfirst, hsecond]) hcoef
    _ = deltaPiConst Jsup kappa * E := by unfold deltaPiConst; ring

#print axioms abs_deltaPrimePiForm_le

/-! ## §5 — the missing COMPANION: `Δ′_source` in pure bond energy

The bridge subtracts `Δ′_π` from a `Δ` that ALREADY contains the (3.10)-level `Δ′_source`. The tree
bounds `Δ′_source` only against `dstarDQuadForm + bondEnergy`
(`LemmaAssemblyNormalized.abs_deltaPrimeQuadFormNormalizedTransported_le`); the `hpi` slot needs a
PURE `‖x‖²` bound. The missing link is an upper bound of `dstarDQuadForm` by `bondEnergy` at
GENERAL `U` — the tree carries only `WitnessInequality`'s `≤ 32·bondEnergy` at `U = 1`. -/

/-- `‖(D_UA)(p)‖² ≤ 4·plaqBondSq A p` — four terms, `(∑xᵢ)² ≤ 4∑xᵢ²`, with `RMap`'s isometry giving
each `A′` component the norm of its bond value (`LemmaAssembly.norm_Aprime*`, REUSED). -/
theorem norm_sq_curl_le_plaqBondSq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlValueCovariant U A p‖ ^ 2
      ≤ 4 * AdalyFormal.Balaban.LemmaAssembly.plaqBondSq A p := by
  have hsum := AdalyFormal.Balaban.DeltaPrime.sum_Aprime_eq_curl U A p
  set x1 := ‖A (p.1, p.2.1.1)‖ with hx1
  set x2 := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ with hx2
  set x3 := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ with hx3
  set x4 := ‖A (p.1, p.2.1.2)‖ with hx4
  have htri : ‖curlValueCovariant U A p‖ ≤ x1 + x2 + x3 + x4 := by
    rw [← hsum]
    have h1 := norm_add_le (AdalyFormal.Balaban.DeltaPrime.AprimeXY A p
        + AdalyFormal.Balaban.DeltaPrime.AprimeYZ U A p
        + AdalyFormal.Balaban.DeltaPrime.AprimeZW U A p)
      (AdalyFormal.Balaban.DeltaPrime.AprimeWX A p)
    have h2 := norm_add_le (AdalyFormal.Balaban.DeltaPrime.AprimeXY A p
        + AdalyFormal.Balaban.DeltaPrime.AprimeYZ U A p)
      (AdalyFormal.Balaban.DeltaPrime.AprimeZW U A p)
    have h3 := norm_add_le (AdalyFormal.Balaban.DeltaPrime.AprimeXY A p)
      (AdalyFormal.Balaban.DeltaPrime.AprimeYZ U A p)
    rw [AdalyFormal.Balaban.LemmaAssembly.norm_AprimeXY,
      AdalyFormal.Balaban.LemmaAssembly.norm_AprimeYZ,
      AdalyFormal.Balaban.LemmaAssembly.norm_AprimeZW,
      AdalyFormal.Balaban.LemmaAssembly.norm_AprimeWX] at *
    linarith [h1, h2, h3]
  have h0 : 0 ≤ ‖curlValueCovariant U A p‖ := norm_nonneg _
  have hplaq : AdalyFormal.Balaban.LemmaAssembly.plaqBondSq A p
      = x1 ^ 2 + x4 ^ 2 + x2 ^ 2 + x3 ^ 2 := rfl
  rw [hplaq]
  nlinarith [htri, h0, sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4),
    sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x3 - x4)]

/-- **`dstarDQuadForm U A ≤ 16·bondEnergy A`, at GENERAL `U`.** `4` from the four-term
Cauchy–Schwarz, `4` from `LemmaAssemblyNormalized.sum_plaqBondSq_eq`'s EXACT incidence identity.
(`WitnessInequality`'s `≤ 32` is the `U = 1` special case, and is beaten by a factor 2.) -/
theorem dstarDQuadForm_le_bondEnergy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    AdalyFormal.Balaban.CovariantHj.dstarDQuadForm U A ≤ 16 * bondEnergy A := by
  rw [AdalyFormal.Balaban.LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq]
  calc ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette L,
          4 * AdalyFormal.Balaban.LemmaAssembly.plaqBondSq A p :=
        Finset.sum_le_sum (fun p _ => norm_sq_curl_le_plaqBondSq U A p)
    _ = 4 * ∑ p : PeriodicLatticePlaquette L,
          AdalyFormal.Balaban.LemmaAssembly.plaqBondSq A p := (Finset.mul_sum _ _ _).symm
    _ = 4 * (4 * bondEnergy A) := by
        rw [AdalyFormal.Balaban.LemmaAssemblyNormalized.sum_plaqBondSq_eq]
    _ = 16 * bondEnergy A := by ring

/-- **`Δ′_source` IN PURE BOND ENERGY**: `|⟨A,Δ′A⟩_norm| ≤ 272·α₀·bondEnergy A`.
`272 = 8·16 + 144`, both factors from already-banked theorems. -/
theorem abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported U A|
      ≤ 272 * α₀ * bondEnergy A := by
  have h := AdalyFormal.Balaban.LemmaAssemblyNormalized.abs_deltaPrimeQuadFormNormalizedTransported_le
    hα₀ U hreg A
  have hd := dstarDQuadForm_le_bondEnergy U A
  have h8 : 8 * α₀ * AdalyFormal.Balaban.CovariantHj.dstarDQuadForm U A
      ≤ 8 * α₀ * (16 * bondEnergy A) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  linarith

#print axioms norm_sq_curl_le_plaqBondSq
#print axioms dstarDQuadForm_le_bondEnergy
#print axioms abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy

/-! ## §6 — the `hpi` SHAPE: from a bond-energy bound to `δ‖x‖²` on the `L²` carrier

**Consumption status, measured 2026-07-31.** `abs_inner_le_of_piForm` (the `Δ′_π` shape) is consumed
by §12's wrapper. `abs_inner_deltaPrimeCLMNormalized_le` (the `Δ′_source` shape) is consumed
**nowhere** — not in this file, not anywhere in `formal/` (this module has zero importers; see the
header). It was written to feed a future `h310W` discharge showing `deltaKCLMNormalized` is itself
coercive despite containing `Δ′_source`; that consumer does not exist. Stated so a reader does not
infer from its presence that something uses it. -/

/-- `‖toLp A‖² = bondEnergy A`, composed from the two primitives that ARE in this import closure
(`BondSU2Space.inner_bondFnL2_eq_covBondInner`, `RegularUDirectCoercivity.covBondInner_eq_bondEnergy`).
`CoercivitySupply.norm_sq_toLp` states the same fact but is NOT reachable from here — checked, not
assumed (`compute/delta_bound/probe1.log`). -/
theorem norm_sq_toLp (A : Bond L → SuTwo) :
    ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 = bondEnergy A := by
  rw [← real_inner_self_eq_norm_sq, AdalyFormal.Balaban.BondSU2Space.inner_bondFnL2_eq_covBondInner,
    AdalyFormal.Balaban.RegularUDirectCoercivity.covBondInner_eq_bondEnergy]

/-- **`hpi` FOR `Δ′_source`** — the exact shape `bridge_from_piExtended_normalized_threeTen`
consumes, at `δ = 272·α₀`, for EVERY `x` on the carrier (not merely for `toLp` of a field). -/
theorem abs_inner_deltaPrimeCLMNormalized_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (x : BondFnL2 L) :
    |(inner ℝ x
        (AdalyFormal.Balaban.DeltaPrimeOperator.deltaPrimeCLMNormalized U x) : ℝ)|
      ≤ 272 * α₀ * ‖x‖ ^ 2 := by
  obtain ⟨A, rfl⟩ : ∃ A : Bond L → SuTwo, x = WithLp.toLp 2 A := ⟨WithLp.ofLp x, rfl⟩
  rw [AdalyFormal.Balaban.DeltaPrimeOperator.inner_deltaPrimeCLMNormalized_eq, norm_sq_toLp]
  exact abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy hα₀ U hreg A

/-- **`hpi` FOR `Δ′_π`** — the same shape at `δ = deltaPiConst Jsup κ`, for any operator `T` whose
diagonal is (3.120)'s form. The Riesz promotion is the only thing carried as a hypothesis, and it is
an IDENTITY, not a bound: nothing about the size of `Δ′_π` is assumed here. -/
theorem abs_inner_le_of_piForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond L → SuTwo) → PeriodicLatticeSite L → SuTwo)
    (T : BondFnL2 L → BondFnL2 L) (Jsup kappa : ℝ)
    (hT : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (T (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm U J (Lam A) A)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) (hk0 : 0 ≤ kappa)
    (hlam : ∀ A : Bond L → SuTwo, siteEnergy (Lam A) ≤ kappa ^ 2 * bondEnergy A)
    (x : BondFnL2 L) :
    |(inner ℝ x (T x) : ℝ)| ≤ deltaPiConst Jsup kappa * ‖x‖ ^ 2 := by
  obtain ⟨A, rfl⟩ : ∃ A : Bond L → SuTwo, x = WithLp.toLp 2 A := ⟨WithLp.ofLp x, rfl⟩
  rw [hT, norm_sq_toLp]
  exact abs_deltaPrimePiForm_le U J (Lam A) A Jsup kappa hJ hk0 (hlam A)

#print axioms norm_sq_toLp
#print axioms abs_inner_deltaPrimeCLMNormalized_le
#print axioms abs_inner_le_of_piForm

/-! ## §7 — the CURVATURE INPUT: `Jsup` from `GaugeRegular α₀`

`J = D*η⁻²Im ∂U`. The pointwise curvature factor is bounded here; the plaquette→bond incidence of
`D*` is bounded generically (a `±`-combination of `m` plaquette values). The exact incidence formula
for `D*` is NOT in this tree, so the second lemma is stated for an arbitrary `m`-term combination
rather than asserted at `m = 4` — a scope statement, not a gap in the bound. -/

/-- **`‖Im U(∂p)‖_F ≤ 6·α₀` for a `GaugeRegular α₀` background.** The estimate is
`LemmaAssembly.abs_deltaPrimeSecondTerm_le`'s internal step (it is not a standalone declaration
there), re-stated at top level here from the SAME two banked inputs
(`frobSq_imHolonomy_le`, `frobNorm_holonomy_sub_one_le`) plus `AlphaAnalyticity.sqrt_two_le`. -/
theorem frobNorm_imHolonomy_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (p : PeriodicLatticePlaquette L) :
    frobNorm (imHolonomy U p) ≤ 6 * α₀ := by
  have h1 : AdalyFormal.Balaban.RMapLipschitz.frobSq (imHolonomy U p)
      ≤ AdalyFormal.Balaban.RMapLipschitz.frobSq
        ((AdalyFormal.Balaban.DeltaPrime.holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
    frobSq_imHolonomy_le U p
  have h2 := frobNorm_holonomy_sub_one_le hα₀ U hreg p
  have h3 : frobNorm (imHolonomy U p) ≤ 4 * Real.sqrt 2 * α₀ := by
    calc frobNorm (imHolonomy U p)
        = Real.sqrt (AdalyFormal.Balaban.RMapLipschitz.frobSq (imHolonomy U p)) :=
          AdalyFormal.Balaban.LemmaAssembly.frobNorm_eq _
      _ ≤ Real.sqrt (AdalyFormal.Balaban.RMapLipschitz.frobSq
            ((AdalyFormal.Balaban.DeltaPrime.holonomyElem U p :
              Matrix (Fin 2) (Fin 2) ℂ) - 1)) := Real.sqrt_le_sqrt h1
      _ = frobNorm ((AdalyFormal.Balaban.DeltaPrime.holonomyElem U p :
            Matrix (Fin 2) (Fin 2) ℂ) - 1) := (AdalyFormal.Balaban.LemmaAssembly.frobNorm_eq _).symm
      _ ≤ 4 * Real.sqrt 2 * α₀ := h2
  have h4 : Real.sqrt 2 ≤ 3 / 2 := sqrt_two_le
  nlinarith [h3, h4, hα₀]

#print axioms frobNorm_imHolonomy_le

/-! ## §8 — WHY THE `HolonomyDomination` REFUTATION DOES NOT TRANSFER

`HolonomyDomination.lean` refutes DOMINATION: `0 ≤ dstarDQuadForm U A + Δ′(U,A)` at every positive
regularity threshold. The question here is BOUNDEDNESS: `|Δ′| ≤ δ·bondEnergy A`. Boundedness
implies domination only through a REVERSE inequality `δ·bondEnergy A ≤ dstarDQuadForm U A`, and that
reverse inequality is false at every positive `δ` — the constant field at the trivial background has
`dstarDQuadForm = 0` and `bondEnergy > 0`. So the refuted statement is strictly stronger and its
refutation carries no information about `δ`. -/

/-- A CONSTANT field has zero curl at the trivial background. -/
theorem curl_trivialU_const_eq_zero (c : SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L))
      (fun _ => c) p = 0 := by
  unfold curlValueCovariant AdalyFormal.Balaban.DeltaPrime.trivialU
  simp

/-- **THE WITNESS**: `dstarDQuadForm = 0` while `bondEnergy > 0`. -/
theorem dstarD_zero_bondEnergy_pos :
    AdalyFormal.Balaban.CovariantHj.dstarDQuadForm
        (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L))
        (fun _ => suTwoWitness) = 0
      ∧ 0 < bondEnergy (fun _ : Bond L => (suTwoWitness : SuTwo)) := by
  constructor
  · rw [AdalyFormal.Balaban.LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [curl_trivialU_const_eq_zero]
    simp
  · have hpos : 0 < ‖(suTwoWitness : SuTwo)‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
    have hne : (Finset.univ : Finset (Bond L)).Nonempty :=
      Finset.univ_nonempty (α := Bond L)
    exact Finset.sum_pos (fun b _ => by positivity) hne

/-- **THE TRANSFER VERDICT, AS A THEOREM.** No positive `δ` makes a bond-energy bound on `Δ′` imply
domination, because the implication needs `δ·bondEnergy ≤ dstarDQuadForm` and that fails at the
constant field. `HolonomyDomination`'s refutation therefore attacks a statement strictly stronger
than the one §4/§5 prove, and does not transfer. -/
theorem no_reverse_bound_at_constant_field (δ : ℝ) (hδ : 0 < δ) :
    ¬ (∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
        (A : Bond L → SuTwo),
        δ * bondEnergy A ≤ AdalyFormal.Balaban.CovariantHj.dstarDQuadForm U A) := by
  intro hall
  obtain ⟨hzero, hposE⟩ := dstarD_zero_bondEnergy_pos (L := L)
  have h := hall (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) (fun _ => suTwoWitness)
  rw [hzero] at h
  nlinarith [h, hposE, hδ]

#print axioms curl_trivialU_const_eq_zero
#print axioms dstarD_zero_bondEnergy_pos
#print axioms no_reverse_bound_at_constant_field

/-! ## §9 — THE FIXED POINT: does `γ_{k+1} = (γ_k − δ)/q²` keep a positive floor?

At `q = 1/ell < 1` the step map is EXPANDING, so `GammaRecursion.uniformStepGamma_of_lt_one`
(REUSED) gives a floor exactly when `δ ≤ γ₀(1 − q²)`. At `ell = 2` that is `δ ≤ (3/4)γ₀`.

**WHERE `q` COMES FROM — WIRED, NOT ASSERTED (repair of a conviction both families returned).** The
numeric instances below previously carried `q := 1/2` as a bare literal, justified only by a
docstring sentence "`1/ell` at `ell = 2`". They now carry
`Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) − 5))` — the (3.16)-WEIGHTED coarse-graining ratio at `d = 3`,
`ell = 2` — and are proved by rewriting through `WeightedQNorm.weighted_q_two_eq_half`, which is the
declaration that computes it. `WeightedQNorm.weighted_const_three` gives the general
`ell^(d−5) = ell⁻²`, i.e. `q = 1/ell`; `WeightedQNorm.weighted_sharp_trivialU` shows the value is
ATTAINED, so it is not a lossy estimate.

Which reading of `q` this is, and why it is the conservative one: `QCLMNorm.qCLM_opNorm_le` gives
the UNWEIGHTED `‖qCLM U ell‖ ≤ √(ell⁻³)` (its companion `QCLMNorm.qCLM_opNorm_lt_one` states only
`< 1`), which is `≈ 0.354` at `ell = 2` and would give a LARGER margin. The weighted value `1/2` is
the source-faithful one and the smaller margin, so every criterion below holds on both readings. -/

/-- The fixed-point criterion, at (3.120)'s measured `δ`. -/
theorem uniformStepGamma_of_deltaPi {γ₀ q Jsup kappa : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hγ : 0 < γ₀) (hfix : deltaPiConst Jsup kappa ≤ γ₀ * (1 - q ^ 2)) :
    AdalyFormal.Balaban.GammaRecursion.UniformStepGamma (deltaPiConst Jsup kappa) q :=
  AdalyFormal.Balaban.GammaRecursion.uniformStepGamma_of_lt_one hq0 hq1 hγ hfix

/-- **THE WEIGHTED `q` AT `ell = 2`, RE-EXPORTED.** `WeightedQNorm.weighted_q_two_eq_half`, named
here so the instances below read as statements about the DERIVED ratio and not about a literal.
Not re-proved: this is that theorem. -/
theorem weightedQ_two : Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5)) = 1 / 2 :=
  AdalyFormal.Balaban.WeightedQNorm.weighted_q_two_eq_half

/-- **THE `Δ′_source` HALF CLOSES AT THE TREE'S OWN NUMBERS.** `δ = 272·normAlpha = 1.36·10⁻⁴`
(§5), `γ₀ = normGamma = 1/2000`, and `q` the weighted ratio at `ell = 2`: the criterion
`δ ≤ (3/4)γ₀ = 3.75·10⁻⁴` HOLDS, with `375/136 ≈ 2.76×` of room (§9a).

**This margin belongs to `Δ′_source`, the (3.10)-level object the tree already bounded — NOT to
`Δ′_π`.** The `Δ′_π` margin at the demo numbers is `375/304 ≈ 1.23×`, a factor `2.24` smaller;
`pi_delta_margin` states both side by side so the two cannot be confused. -/
theorem uniformStepGamma_at_source_delta :
    AdalyFormal.Balaban.GammaRecursion.UniformStepGamma
      (272 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha)
      (Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5))) := by
  rw [weightedQ_two]
  refine AdalyFormal.Balaban.GammaRecursion.uniformStepGamma_of_lt_one
    (γ₀ := AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma)
    (by norm_num) (by norm_num)
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma_pos ?_
  unfold AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  norm_num

/-- **THE `Δ′_source` MARGIN, EXACTLY.** `272·normAlpha = 17/125000` and `(3/4)·normGamma = 3/8000`.
The criterion IS met, and the ratio of threshold to `δ` is `375/136 ≈ 2.757` (`pi_delta_margin`
states that ratio exactly, together with the `Δ′_π` one).

**⚠ CORRECTED 2026-07-31.** ~~"the ratio is `2.7…`, so the criterion is not met by a hair"~~ —
retained struck: that sentence read as if the criterion FAILED narrowly. It is met, with a factor
`2.76` of room. -/
theorem source_delta_margin :
    272 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha = 17 / 125000
      ∧ (3 / 4 : ℝ) * AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma = 3 / 8000 := by
  unfold AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  norm_num

/-- **A `Δ′_π` POINT THAT CLOSES.** With `κ = 1` the criterion needs `76·Jsup ≤ 3/8000`, i.e.
`Jsup ≤ 3/608000 ≈ 4.9·10⁻⁶`. At `Jsup = 4·10⁻⁶` it holds — with `375/304 ≈ 1.23×` of room, which
is THIS form's margin (§9a).

Both `κ = 1` and `Jsup = 4·10⁻⁶` are CHOSEN points, not derived values. `KappaBound.lean` has since
derived `κ ≤ √768 ≈ 27.71` (conditionally on an open block-Poincaré input — §9b); at that `κ` this
point does not survive — see §9b. -/
theorem uniformStepGamma_at_piDelta :
    AdalyFormal.Balaban.GammaRecursion.UniformStepGamma
      (deltaPiConst (1 / 250000) 1) (Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5))) := by
  rw [weightedQ_two]
  refine uniformStepGamma_of_deltaPi
    (γ₀ := AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma)
    (by norm_num) (by norm_num)
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma_pos ?_
  unfold deltaPiConst AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  norm_num

/-- **MUST-FIRE CONTROL 1.** At `Jsup = 10⁻³, κ = 1` the criterion FAILS: `δ = 0.076` against
`3.75·10⁻⁴`. So the threshold on `Jsup` is load-bearing, not decorative. Stated at the same derived
`q` as the instances it controls. -/
theorem fixedPoint_criterion_fails_at_thousandth :
    ¬ (deltaPiConst (1 / 1000) 1
        ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
          * (1 - Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5)) ^ 2)) := by
  rw [weightedQ_two]
  unfold deltaPiConst AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  norm_num

/-- **MUST-FIRE CONTROL 2 — the failure is not abstract.** At that same point the bridge's OWN
hypothesis `0 < γ − δ` is already violated at step 1: the iterate goes NEGATIVE immediately. -/
theorem gammaSeq_negative_at_thousandth :
    AdalyFormal.Balaban.GammaRecursion.gammaSeq
      AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
      (deltaPiConst (1 / 1000) 1) (Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5))) 1 < 0 := by
  rw [weightedQ_two]
  show (AdalyFormal.Balaban.GammaRecursion.gammaSeq
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
    (deltaPiConst (1 / 1000) 1) (1 / 2) 0 - deltaPiConst (1 / 1000) 1) / (1 / 2 : ℝ) ^ 2 < 0
  rw [AdalyFormal.Balaban.GammaRecursion.gammaSeq_zero]
  unfold deltaPiConst AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  norm_num

/-- **MUST-NOT-FIRE CONTROL.** `deltaPiConst` is not vacuously small: it is STRICTLY positive at
every positive `(Jsup, κ)`, so §9's criterion is a real constraint and never trivially satisfied. -/
theorem deltaPiConst_pos {Jsup kappa : ℝ} (hJ : 0 < Jsup) (hk : 0 < kappa) :
    0 < deltaPiConst Jsup kappa := by
  unfold deltaPiConst
  have : 0 < 28 + 48 * kappa := by linarith
  positivity

#print axioms weightedQ_two
#print axioms uniformStepGamma_of_deltaPi
#print axioms uniformStepGamma_at_source_delta
#print axioms source_delta_margin
#print axioms uniformStepGamma_at_piDelta
#print axioms fixedPoint_criterion_fails_at_thousandth
#print axioms gammaSeq_negative_at_thousandth
#print axioms deltaPiConst_pos

/-! ### §9a — THE TWO MARGINS ARE DIFFERENT NUMBERS, ATTACHED TO DIFFERENT OBJECTS

Both prosecutions flagged that the headline `≈2.76×` is the `Δ′_source` margin while the object
CMP99b p.419 actually defers is `Δ′_π`, whose margin at the same demo numbers is `≈1.23×` — a factor
`2.24` smaller. The two numbers are pinned here in exact rationals, in one theorem, so no reader can
attach one to the other. -/

/-- **BOTH MARGINS, EXACTLY, SIDE BY SIDE.**

* `Δ′_source` (§5's object): `δ = 17/125000`, threshold `3/8000`, margin **`375/136 ≈ 2.757×`**.
* `Δ′_π` (§4's object, the one p.419 defers): `δ = deltaPiConst (1/250000) 1 = 19/62500`, same
  threshold, margin **`375/304 ≈ 1.234×`**.

The final conjunct is the MUST-FIRE half: the two margins are not equal, so quoting the first for
the second is an error of a factor `2.24` and not a rounding. -/
theorem pi_delta_margin :
    (3 / 8000 : ℝ) = (375 / 136) * (17 / 125000)
      ∧ (3 / 8000 : ℝ) = (375 / 304) * (19 / 62500)
      ∧ deltaPiConst (1 / 250000) 1 = 19 / 62500
      ∧ (375 / 304 : ℝ) < 375 / 136 := by
  unfold deltaPiConst
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms pi_delta_margin

/-! ### §9b — THE `κ` LANDING: THE DEMO INSTANCES ARE OPTIMISTIC, AND BY HOW MUCH

`§9`'s `Δ′_π` instance takes `κ = 1`. That was a stand-in, disclosed as such, and both prosecutions
returned OVERCLAIMED on it because nothing in the tree bounded `κ` at all.

**`KappaBound.lean` has since bounded it**, without ever encoding `G′`: `KappaBound.hlam_at_kappa_sq_768`
gives `siteEnergy λ ≤ 768·bondEnergy A`, i.e. `κ ≤ √768 = 16√3 ≈ 27.71`
(`KappaBound.kappa_bounds`, `KappaBound.kappa_lower_sharp`), and it composes that with the criterion
in `KappaBound.criterion_fails_at_normAlpha` and `KappaBound.criterion_closes_at_four_e_minus_ten`.

**⚠ THAT BOUND IS CONDITIONAL, AND THIS FILE MUST NOT LAUNDER IT (LAW-12 / never build on deferred
claims). Read at the source, 2026-07-31:** `KappaBound.hlam_at_kappa_sq_768` carries FOUR
hypotheses — `hweak`, `hPoin` (the block-Poincaré inequality with constant `8`), `hadj` (the `D*`
adjoint RELATION) and `hproj`. The `hPoin` input is assembled by
`KappaBound.poincare_assembly_two`, whose own `hblock` hypothesis — the per-block inequality — is
**open**, and is named by `KappaBound.lean` itself as "WHAT REMAINS, EXACTLY ONE THING". A separate
lane was working on it while this repair ran.

So `κ ≤ √768` is **not** an unconditional theorem of this tree. Nothing below depends on it being
one: the four theorems in this section are statements about the real number `√768`, proved from
`√768² = 768` alone, of the form *"AT `κ = √768`, the criterion does/does not close"*. They are
exactly as true if `hblock` never closes; what would change is whether `√768` is the right `κ` to
evaluate at. The demo's `κ = 1` remains a chosen point either way.

**`KappaBound` is NOT imported here** — a concurrent lane was compiling it while this repair ran
(LAW-4), and it states its own inverse abstention for the same reason. So the consequences are
RE-DERIVED below against *this* file's `deltaPiConst`; `KappaBound` proves the same statements
against its own duplicate `deltaPiConstLocal`, which is `Jsup·κ·(28+48κ)` verbatim. Disclosed
duplication, not novelty. What is NOT re-derived here and is taken from `KappaBound` by citation is
the *provenance* of the number `√768` — the block-Poincaré route that produces it. Below, `√768` is
simply a real number, and every statement about it is proved from `√768² = 768`. -/

/-- `27 < √768 < 28`. Duplicate of `KappaBound.kappa_bounds` (not imported — see §9b), re-proved in
three lines from `Real.sq_sqrt`. -/
theorem sqrt_768_bounds : (27 : ℝ) < Real.sqrt 768 ∧ Real.sqrt 768 < 28 := by
  have hsq : Real.sqrt 768 ^ 2 = 768 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 768 := Real.sqrt_nonneg _
  constructor
  · nlinarith [hsq, hnn]
  · nlinarith [hsq, hnn]

/-- **HOW OPTIMISTIC THE `κ = 1` DEMO IS — TWO DIFFERENT RATIOS, BOTH STATED.**

The two are routinely confused, so both are pinned:

* in `κ` itself the demo understates by a factor between `27` and `28` (`sqrt_768_bounds`);
* in `δ` — the quantity the criterion actually tests — the understatement is between `495` and
  `496`, because `deltaPiConst` is QUADRATIC in `κ`: `√768(28+48√768)/76 ≈ 495.3`.

So "optimistic by ≈27.7×" is true of `κ` and FALSE of `δ`. -/
theorem deltaPiConst_kappa_ratio {Jsup : ℝ} (hJ : 0 < Jsup) :
    495 * deltaPiConst Jsup 1 < deltaPiConst Jsup (Real.sqrt 768)
      ∧ deltaPiConst Jsup (Real.sqrt 768) < 496 * deltaPiConst Jsup 1 := by
  obtain ⟨hlo, hhi⟩ := sqrt_768_bounds
  have hsq : Real.sqrt 768 ^ 2 = 768 := Real.sq_sqrt (by norm_num)
  unfold deltaPiConst
  constructor
  · nlinarith [hlo, hhi, hsq, hJ]
  · nlinarith [hlo, hhi, hsq, hJ]

/-- **AT `κ = √768`, THE CRITERION FAILS AT THE TREE'S OWN REGULARITY RADIUS.** With
`Jsup = 24·normAlpha` (§10's chain at `η⁻² = 1`) and `κ = √768`, `δ` STRICTLY EXCEEDS `(3/4)γ₀`.
It asserts nothing about whether `√768` IS `κ` (§9b).
Same statement as `KappaBound.criterion_fails_at_normAlpha`, here against `deltaPiConst`.

**⚠ DO NOT ATTRIBUTE THIS FAILURE TO `κ`.** Caught by this lane's own mutation battery
(`compute/delta_repair/mutants/M2_kappa_one_not_768`): substituting `√1` for `√768` leaves this
statement TRUE, so that mutation does not fire and `κ` is not what breaks it. At
`Jsup = 24·normAlpha = 1.2·10⁻⁵` the criterion fails **already at `κ = 1`** — `δ = 9.12·10⁻⁴`
against a threshold of `3.75·10⁻⁴` — which `criterion_fails_at_normAlpha_at_kappa_one` below states
outright. The reason §9's demo instance closes is not its `κ` but its smaller `Jsup = 4·10⁻⁶`,
three times below `24·normAlpha`.

What `κ` DOES cost is stated exactly by `deltaPiConst_kappa_ratio`: a factor between `495` and `496`
in `δ`, hence the same factor in the admissible `α₀` (§13). -/
theorem criterion_fails_at_normAlpha_at_kappa_sqrt768 :
    ¬ (deltaPiConst (24 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha) (Real.sqrt 768)
        ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
          * (1 - Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5)) ^ 2)) := by
  rw [weightedQ_two]
  obtain ⟨hlo, hhi⟩ := sqrt_768_bounds
  unfold deltaPiConst AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  intro hc
  nlinarith [hlo, hhi, hc]

/-- **AND WHERE IT DOES CLOSE AT `κ = √768`: `α₀ ≤ 4·10⁻¹⁰`**, about `1/1250` of `normAlpha`.
Same statement as `KappaBound.criterion_closes_at_four_e_minus_ten`, here against `deltaPiConst`.
`KappaBound.criterion_fails_at_four_point_three_e_minus_ten` pins the boundary from above, so this
is not an arbitrarily small number chosen to make the statement true. -/
theorem criterion_closes_at_four_e_minus_ten_at_kappa_sqrt768 :
    deltaPiConst (24 * (4 / 10 ^ 10 : ℝ)) (Real.sqrt 768)
      ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
        * (1 - Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5)) ^ 2) := by
  rw [weightedQ_two]
  obtain ⟨hlo, hhi⟩ := sqrt_768_bounds
  have hnn : (0 : ℝ) ≤ Real.sqrt 768 := Real.sqrt_nonneg _
  unfold deltaPiConst AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  nlinarith [hlo, hhi, hnn]

/-- **MUST-NOT-FIRE CONTROL FOR THE `κ` ATTRIBUTION.** The failure at `Jsup = 24·normAlpha` is NOT
caused by `κ`: it happens already at `κ = 1`, where `δ = 24·normAlpha·76 = 57/62500 = 9.12·10⁻⁴`
against the threshold `3/8000 = 3.75·10⁻⁴`.

Without this theorem a reader would take `criterion_fails_at_normAlpha_at_kappa_sqrt768` as evidence
that the landed `κ` is what closes the route off. It is not; at this `Jsup` the route was already
closed off. `κ`'s actual cost is `deltaPiConst_kappa_ratio`'s factor `495`–`496`. -/
theorem criterion_fails_at_normAlpha_at_kappa_one :
    ¬ (deltaPiConst (24 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha) 1
        ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
          * (1 - Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5)) ^ 2)) := by
  rw [weightedQ_two]
  unfold deltaPiConst AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  norm_num

#print axioms sqrt_768_bounds
#print axioms deltaPiConst_kappa_ratio
#print axioms criterion_fails_at_normAlpha_at_kappa_sqrt768
#print axioms criterion_closes_at_four_e_minus_ten_at_kappa_sqrt768
#print axioms criterion_fails_at_normAlpha_at_kappa_one

/-! ## §10 — the `D*` INCIDENCE, and `Jsup` from `GaugeRegular α₀`

`J = D*η⁻²Im ∂U`. `D*` sends a plaquette function to a bond function by combining the plaquettes
that contain the bond with orientation signs — four of them in `d = 3`. The exact index formula for
`D*` is NOT in this tree (the tree carries `curlAdjoint` only on the `L²` carriers, not as a
pointwise plaquette-to-bond formula), so the arity `4` is carried as the SHAPE of the combination
and everything else is proved. -/

/-- `‖c₁ − c₂ + c₃ − c₄‖_F ≤ 4·m` when each `‖cᵢ‖_F ≤ m`. Proved through
`LemmaAssembly.frobSq_add_le` (REUSED) rather than a Frobenius triangle inequality, because
`BlockingLinkEstimate.frobNorm_add_le` is NOT in this import closure — checked
(`compute/delta_bound/probe2.log`), not assumed. -/
theorem frobNorm_four_term_le (c1 c2 c3 c4 : Matrix (Fin 2) (Fin 2) ℂ) (m : ℝ)
    (h1 : frobNorm c1 ≤ m) (h2 : frobNorm c2 ≤ m) (h3 : frobNorm c3 ≤ m)
    (h4 : frobNorm c4 ≤ m) :
    frobNorm (c1 - c2 + c3 - c4) ≤ 4 * m := by
  have hm : 0 ≤ m := le_trans (frobNorm_nonneg c1) h1
  have hfs : ∀ c : Matrix (Fin 2) (Fin 2) ℂ, frobNorm c ≤ m →
      AdalyFormal.Balaban.RMapLipschitz.frobSq c ≤ m ^ 2 := by
    intro c hc
    have := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq c
    nlinarith [hc, frobNorm_nonneg c, this]
  have e12 : AdalyFormal.Balaban.RMapLipschitz.frobSq (c1 - c2) ≤ 4 * m ^ 2 := by
    have h := AdalyFormal.Balaban.LemmaAssembly.frobSq_add_le c1 (-c2)
    rw [← sub_eq_add_neg, AdalyFormal.Balaban.LemmaAssembly.frobSq_neg] at h
    linarith [hfs c1 h1, hfs c2 h2, h]
  have e34 : AdalyFormal.Balaban.RMapLipschitz.frobSq (c3 - c4) ≤ 4 * m ^ 2 := by
    have h := AdalyFormal.Balaban.LemmaAssembly.frobSq_add_le c3 (-c4)
    rw [← sub_eq_add_neg, AdalyFormal.Balaban.LemmaAssembly.frobSq_neg] at h
    linarith [hfs c3 h3, hfs c4 h4, h]
  have esum : AdalyFormal.Balaban.RMapLipschitz.frobSq (c1 - c2 + (c3 - c4)) ≤ 16 * m ^ 2 := by
    have h := AdalyFormal.Balaban.LemmaAssembly.frobSq_add_le (c1 - c2) (c3 - c4)
    linarith [e12, e34, h]
  have hre : c1 - c2 + c3 - c4 = c1 - c2 + (c3 - c4) := by abel
  rw [hre]
  have hfn := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq (c1 - c2 + (c3 - c4))
  nlinarith [esum, hfn, frobNorm_nonneg (c1 - c2 + (c3 - c4)), hm]

/-- **`Jsup ≤ 24·η⁻²·α₀`.** The whole chain from the regularity hypothesis to the only curvature
input of §4's bound: `‖Im U(∂p)‖_F ≤ 6α₀` (§7) times the four-term `D*` combination (above) times
the scale factor. -/
theorem frobNorm_current_le {α₀ etaInvSq : ℝ} (hα₀ : 0 ≤ α₀) (hη : 0 ≤ etaInvSq)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (pl : Bond L → Fin 4 → PeriodicLatticePlaquette L)
    (hJ : ∀ b, J b = (etaInvSq : ℂ) •
      (imHolonomy U (pl b 0) - imHolonomy U (pl b 1)
        + imHolonomy U (pl b 2) - imHolonomy U (pl b 3))) (b : Bond L) :
    frobNorm (J b) ≤ 24 * etaInvSq * α₀ := by
  have hcomb : frobNorm (imHolonomy U (pl b 0) - imHolonomy U (pl b 1)
      + imHolonomy U (pl b 2) - imHolonomy U (pl b 3)) ≤ 4 * (6 * α₀) :=
    frobNorm_four_term_le _ _ _ _ _
      (frobNorm_imHolonomy_le hα₀ U hreg _) (frobNorm_imHolonomy_le hα₀ U hreg _)
      (frobNorm_imHolonomy_le hα₀ U hreg _) (frobNorm_imHolonomy_le hα₀ U hreg _)
  set M := imHolonomy U (pl b 0) - imHolonomy U (pl b 1)
    + imHolonomy U (pl b 2) - imHolonomy U (pl b 3) with hM
  have hsmul : frobNorm ((etaInvSq : ℂ) • M) = etaInvSq * frobNorm M := by
    have hsq : AdalyFormal.Balaban.RMapLipschitz.frobSq ((etaInvSq : ℂ) • M)
        = etaInvSq ^ 2 * AdalyFormal.Balaban.RMapLipschitz.frobSq M := by
      rw [AdalyFormal.Balaban.LemmaAssembly.frobSq_smul]
      rw [Complex.normSq_ofReal]
      ring
    have h1 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq ((etaInvSq : ℂ) • M)
    have h2 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq M
    have h3 : frobNorm ((etaInvSq : ℂ) • M) ^ 2 = (etaInvSq * frobNorm M) ^ 2 := by
      rw [h1, hsq, ← h2]; ring
    have h4 : 0 ≤ frobNorm ((etaInvSq : ℂ) • M) := frobNorm_nonneg _
    have h5 : 0 ≤ etaInvSq * frobNorm M := mul_nonneg hη (frobNorm_nonneg _)
    nlinarith [h3, h4, h5]
  rw [hJ b, hsmul]
  have hMn : 0 ≤ frobNorm M := frobNorm_nonneg _
  nlinarith [hcomb, hη, hMn]

#print axioms frobNorm_four_term_le
#print axioms frobNorm_current_le

/-! ## §11 — `κ` FROM THE SITE-LEVEL GAP

`λ = G'RD*A` is defined by inverting the site operator on `N(Q')`. Whatever that operator is, a
LOWER bound `m` on it over the relevant subspace plus an upper bound `r` on the source `RD*A`
determines `κ = r/m` — and `r` is itself controlled by §3's `bondEnergy (D_Uλ) ≤ 12·siteEnergy λ`
(the covariant gradient's operator norm is `≤ 2√3`, and `D*` has the same norm as `D`).

**⚠ THIS SECTION'S REDUCTION IS UNCONSUMED, AND HAS BEEN OVERTAKEN. Measured 2026-07-31.**
`siteEnergy_le_of_gap` has **zero consumers** in `formal/` (the single grep hit outside this file is
`KappaBound.lean`'s import note recording that it is deliberately NOT reused). Its two hypotheses —
a lower spectral bound `m` on the site operator, and an upper bound `r` on `RD*A` — are discharged
nowhere in this tree, so `κ = r/m` parks the difficulty rather than resolving it. Both prosecutions
returned OVERCLAIMED on the `κ` framing for exactly this reason.

`KappaBound.lean` has since done the job by a different route that reaches an actual number:
`KappaBound.siteEnergy_le_of_poincare` + `KappaBound.hlam_at_kappa_sq_768` give
`siteEnergy λ ≤ 768·bondEnergy A`, i.e. `κ ≤ √768`, via a block-Poincaré inequality and the adjoint
RELATION for `D*` — with `G′` and `R` eliminated structurally rather than encoded. That route is
better than this one but is **not yet unconditional**: `hlam_at_kappa_sq_768` carries four
hypotheses and its block-Poincaré input traces to an open `hblock` (§9b reads this at the source).
§9b prices the consequence at `κ = √768` without asserting the bound. This section is retained as
the honest record of the weaker reduction it is, not as the live route. -/

/-- Cauchy–Schwarz for `covSiteInner`. -/
theorem abs_covSiteInner_le (f g : PeriodicLatticeSite L → SuTwo) :
    |AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner f g|
      ≤ Real.sqrt (siteEnergy f) * Real.sqrt (siteEnergy g) := by
  have hpt : ∀ y : PeriodicLatticeSite L, |hsInner (f y) (g y)| ≤ ‖f y‖ * ‖g y‖ := by
    intro y
    rw [← inner_eq_hsInner]
    exact abs_real_inner_le_norm _ _
  have h1 : |AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner f g|
      ≤ ∑ y : PeriodicLatticeSite L, ‖f y‖ * ‖g y‖ := by
    unfold AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ => hpt y))
  refine h1.trans ?_
  have h2 := sum_mul_le_sqrt_mul_sqrt (fun y : PeriodicLatticeSite L => ‖f y‖)
    (fun y : PeriodicLatticeSite L => ‖g y‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  rwa [show (∑ y : PeriodicLatticeSite L, ‖f y‖ ^ 2) = siteEnergy f from rfl,
    show (∑ y : PeriodicLatticeSite L, ‖g y‖ ^ 2) = siteEnergy g from rfl] at h2

/-- **`κ = r/m`.** If the gauge parameter `λ` satisfies the variational inequality
`m·siteEnergy λ ≤ ⟨λ, src⟩` supplied by inverting the site operator, and the source `src = RD*A`
obeys `siteEnergy src ≤ r²·bondEnergy A`, then `siteEnergy λ ≤ (r/m)²·bondEnergy A` — which is
exactly §4's `hlam` at `κ = r/m`. -/
theorem siteEnergy_le_of_gap
    (lam src : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (m r : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r)
    (hgap : m * siteEnergy lam ≤ AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hsrc : siteEnergy src ≤ r ^ 2 * bondEnergy A) :
    siteEnergy lam ≤ (r / m) ^ 2 * bondEnergy A := by
  have hS0 : 0 ≤ siteEnergy lam := siteEnergy_nonneg lam
  have hE0 : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hcs : AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src
      ≤ Real.sqrt (siteEnergy lam) * Real.sqrt (siteEnergy src) :=
    le_trans (le_abs_self _) (abs_covSiteInner_le lam src)
  have hsrcsq : Real.sqrt (siteEnergy src) ≤ r * Real.sqrt (bondEnergy A) := by
    have := Real.sqrt_le_sqrt hsrc
    rwa [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr] at this
  have hchain : m * siteEnergy lam
      ≤ Real.sqrt (siteEnergy lam) * (r * Real.sqrt (bondEnergy A)) := by
    refine le_trans hgap (le_trans hcs ?_)
    exact mul_le_mul_of_nonneg_left hsrcsq (Real.sqrt_nonneg _)
  have hsq : Real.sqrt (siteEnergy lam) * Real.sqrt (siteEnergy lam) = siteEnergy lam :=
    Real.mul_self_sqrt hS0
  have hEsq : Real.sqrt (bondEnergy A) * Real.sqrt (bondEnergy A) = bondEnergy A :=
    Real.mul_self_sqrt hE0
  have hs0 : 0 ≤ Real.sqrt (siteEnergy lam) := Real.sqrt_nonneg _
  have he0 : 0 ≤ Real.sqrt (bondEnergy A) := Real.sqrt_nonneg _
  -- `m·s² ≤ s·r·e` gives `m·s ≤ r·e`, hence `s ≤ (r/m)·e`, hence `s² ≤ (r/m)²·e²`
  have hstep : m * Real.sqrt (siteEnergy lam) ≤ r * Real.sqrt (bondEnergy A) := by
    rcases eq_or_lt_of_le hs0 with hz | hpos
    · nlinarith [hz, hm, he0, hr]
    · nlinarith [hchain, hsq, hpos]
  have hdiv : Real.sqrt (siteEnergy lam) ≤ (r / m) * Real.sqrt (bondEnergy A) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith [hstep]
  have hrm : 0 ≤ r / m := div_nonneg hr (le_of_lt hm)
  nlinarith [hdiv, hs0, hsq, hEsq, he0, hrm]

#print axioms abs_covSiteInner_le
#print axioms siteEnergy_le_of_gap

/-! ## §12 — A SHAPE DEMONSTRATION INTO A SOCKET THAT IS PROVED DEAD

**⚠ READ THIS BEFORE READING THE THEOREM. REBILLED 2026-07-31 on the convictions of two
de-correlated prosecutions** (`compute/delta_prosecution/VERDICT.md` item F;
`compute/kimi_delta/VERDICT.md` Q5's caveat and ninth issue).

`bridge_at_measured_deltaPi` below is a thin wrapper of
`RecursiveBridge.bridge_from_piExtended_normalized_threeTen`. Its content is **exactly one thing**:
that §4/§6's measured bound fits that consumer's `hpi` slot — same carrier `BondFnL2 L`, same norm,
same two-sided shape. That fit is real and is what Kimi's Q5 verified.

**What it is NOT: evidence that the bridge produces a coercivity constant.** The consumer it wraps
was already proved witness-less, three days before this module was first committed, in a file this
module imports, and the original §12 docstring did not say so. Two independent obstructions, neither
of which discharging `hpi` touches:

1. `RecursiveBridge.fineMapOf_surjective_of_hG1` — supplying `hG1` MEANS exhibiting a right inverse
   of `Δ_π + P + Q*aQ`, the content CMP99b defers (p.428's `(QG₁Q*)⁻¹`, p.419's promised bounds).
   Restated for this file's own fine operator as `bridge_hG1_slot_forces_surjective` below.
2. `RecursiveBridge.h310_unrestricted_forces_zero_norm_at_witnessU` +
   `RecursiveBridge.toLp_deltaWitnessConfig_ne_zero` — at the tree's one concrete background an
   UNRESTRICTED `h310W` with `γ > 0` forces a field that is proved nonzero to have zero norm.
   Composed to outright `False` as `bridge_h310W_slot_unsatisfiable_at_witnessU` below, and then
   `bridge_at_measured_deltaPi_hypotheses_unsatisfiable_at_witnessU` derives `False` from the
   wrapper's ENTIRE binder list — fed to the wrapper itself, so the list is type-identical and not a
   hand-copied lookalike.

**Deepened since those prosecutions, by `BridgeRestricted.lean`** (`compute/bridge_restricted/PROGRESS.md`;
NOT imported — it had no `.olean` and its source was under a live lane's hand while this repair ran,
so these are citations, not consumed theorems):

* `BridgeRestricted.bridge_hyps_false_of_W_subset_kerQ` — the obvious repair, restricting `W`, is a
  PROVED IMPOSSIBILITY: `hGW`/`hTdef`/`hTS` force `Q` to carry `W` ONTO `K`, so `W ⊆ ker Q` makes the
  hypothesis set contradictory. `BridgeRestricted.bridge_at_VReg_hypotheses_unsatisfiable` feeds the
  full binder list at `W := VReg U` and derives `False`.
* `BridgeRestricted.H310A_false_at_curvedRegularU` — the `a`-augmented repair fails too: at
  `curvedRegularU` the alternating axial field is a null direction of `Δ_k` that `Q` annihilates, so
  `H310A` is false for EVERY `γ > 0` and EVERY `a`.

**The surviving chain, and why the measured `δ` is not fed into it here.**
`BridgeRestricted.bridge_source_chain_hDPa_at_curvedRegularU` is the chain that does not route
through the refuted hypotheses. It takes the coercivity input `hDPa` DIRECTLY and **has no `hpi`
slot at all**, so there is nothing in it for §4/§6's bound to discharge. The declaration in that
file that does carry an `hpi` slot of this bound's exact shape is
`BridgeRestricted.alternating_field_forces_P_coercive`, which would consume `δ` and return
`(γ − δ)‖v‖² ≤ ⟨v, P v⟩` at the alternating field. Wiring the measured `δ` into it is a genuine
piece of work and it is NOT done here, for one reason only: `BridgeRestricted.lean` cannot be
imported from this lane without building a live lane's uncompiled file into the shared `.lake/build`.
That is a write-scope collision, recorded as such in `compute/delta_repair/PROGRESS.md`, not a
mathematical obstruction.

So: the theorem below stays, because its shape-fit content is real and was verified; it is billed as
a SHAPE demonstration and nothing more. -/

set_option maxHeartbeats 1000000 in
/-- **`bridge_from_piExtended_normalized_threeTen` AT `δ = deltaPiConst Jsup κ`.** The `hpi`
hypothesis is DISCHARGED by §4/§6; every other hypothesis is passed through unchanged.

**⚠ THE CONSUMER THIS WRAPS HAS NO WITNESS ANYWHERE IN THIS TREE** — see §12's header and the three
theorems after this one. This declaration demonstrates that the measured `δ` FITS the slot; it does
not, and cannot, show the slot is fillable. Do not read it as evidence that the fixed point closes
on anything. -/
theorem bridge_at_measured_deltaPi {K : Type*} [SeminormedAddCommGroup K]
    [InnerProductSpace ℝ K] [Nontrivial K]
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond L → SuTwo) → PeriodicLatticeSite L → SuTwo)
    (DeltaPrimePi P : BondFnL2 L → BondFnL2 L) (W : BondFnL2 L → Prop)
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (T S : K →L[ℝ] K) (a γ q Jsup kappa : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hRiesz : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (DeltaPrimePi (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm U J (Lam A) A)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) (hk0 : 0 ≤ kappa)
    (hlam : ∀ A : Bond L → SuTwo, siteEnergy (Lam A) ≤ kappa ^ 2 * bondEnergy A)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hGW : ∀ B : K, W (G (Qstar B)))
    (hTdef : ∀ B : K, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 L,
      AdalyFormal.Balaban.RecursiveBridge.fineMapOf
        (AdalyFormal.Balaban.RecursiveBridge.piExtendedMap
          (fun y => AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U y) DeltaPrimePi)
        P Q Qstar a (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγδ : 0 < γ - deltaPiConst Jsup kappa) (hq : 0 < q) (ha : 0 ≤ a)
    (h310W : ∀ A : Bond L → SuTwo, W (WithLp.toLp 2 A) →
      γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2
        ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected U A)
    (hQ : ∀ x : BondFnL2 L, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    ((γ - deltaPiConst Jsup kappa) / q ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 :=
  AdalyFormal.Balaban.RecursiveBridge.bridge_from_piExtended_normalized_threeTen
    U DeltaPrimePi P W Q Qstar G T S a γ (deltaPiConst Jsup kappa) q hadj hPiSym
    (abs_inner_le_of_piForm U J Lam DeltaPrimePi Jsup kappa hRiesz hJ hk0 hlam)
    hPpos hPsym hGW hTdef hG1 hTS hγδ hq ha h310W hQ B

#print axioms bridge_at_measured_deltaPi

/-! ### §12a — THE DEADNESS, AS THEOREMS IN THIS FILE RATHER THAN AS A CITATION

The header above cites `RecursiveBridge` §9f for the two obstructions. A citation is not a
certificate, and the previous version of this module carried neither. The three statements below
name `bridge_at_measured_deltaPi`'s OWN hypothesis slots and say what supplying them costs — the
third by feeding the wrapper its entire binder list and deriving `False`. -/

/-- **THE `hG1` SLOT, PRICED.** Supplying `bridge_at_measured_deltaPi`'s `hG1` — character-for-
character the binder above — entails that this file's own fine operator
`Δ_π + P + Q*aQ` (built on `deltaKCLMNormalized U`) is SURJECTIVE on the bond carrier. That is the
inversion CMP99b p.428 defers. `RecursiveBridge.fineMapOf_surjective_of_hG1` REUSED (LAW-19), here
instantiated at this module's fine operator so the price is attached to this module's theorem.

The conclusion is deliberately weaker than the hypothesis (`Function.Surjective`, not a restatement)
— that weakness is the honest point: **the work is in supplying `hG1`, never in deriving anything
from it.** -/
theorem bridge_hG1_slot_forces_surjective {K : Type*} [SeminormedAddCommGroup K]
    [InnerProductSpace ℝ K]
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi P : BondFnL2 L → BondFnL2 L)
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L) (G : BondFnL2 L → BondFnL2 L) (a : ℝ)
    (hG1 : ∀ x : BondFnL2 L,
      AdalyFormal.Balaban.RecursiveBridge.fineMapOf
        (AdalyFormal.Balaban.RecursiveBridge.piExtendedMap
          (fun y => AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U y) DeltaPrimePi)
        P Q Qstar a (G x) = x) :
    Function.Surjective
      (AdalyFormal.Balaban.RecursiveBridge.fineMapOf
        (AdalyFormal.Balaban.RecursiveBridge.piExtendedMap
          (fun y => AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U y) DeltaPrimePi)
        P Q Qstar a) :=
  AdalyFormal.Balaban.RecursiveBridge.fineMapOf_surjective_of_hG1 _ P Q Qstar G a hG1

/-- **THE `h310W` SLOT IS UNSATISFIABLE AT THE TREE'S ONE CONCRETE BACKGROUND.** Take
`bridge_at_measured_deltaPi` at `L := witnessL`, `U := witnessU` and the unrestricted subspace
`W ≡ True` — the shape the `h310W` binder has when no restriction is imposed. Then the binder alone
yields `False`, at every `γ > 0`, however small `δ` is.

`RecursiveBridge` §9f proved this in two halves and left the last step — `‖v‖ = 0 → v = 0` — open
IN PLACE, describing it as a Lean instance-diamond artifact rather than a mathematical gap. **It is
closed here**: `norm_eq_zero` resolves on `BondFnL2 witnessL` without any bundling gymnastics, so the
two halves compose to `False` in one line. (`RecursiveBridge.lean` is outside this lane's write
scope, so the composition is stated here rather than there.)

This does NOT rule out other intended backgrounds `U`: it says the tree contains no `U` at which the
unrestricted hypothesis holds, and `BridgeRestricted` (cited in §12's header) proves the two obvious
ways of restricting it are themselves contradictory. -/
theorem bridge_h310W_slot_unsatisfiable_at_witnessU (γ : ℝ) (hγ : 0 < γ)
    (h310W : ∀ A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
      (fun _ : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL => True)
          (WithLp.toLp 2 A) →
      γ * ‖(WithLp.toLp 2 A : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ^ 2
        ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
            AdalyFormal.Balaban.CovariantOperators.witnessU A) :
    False := by
  have h := AdalyFormal.Balaban.RecursiveBridge.h310_unrestricted_forces_zero_norm_at_witnessU
    γ hγ (fun A => h310W A trivial)
  exact AdalyFormal.Balaban.RecursiveBridge.toLp_deltaWitnessConfig_ne_zero (norm_eq_zero.1 h)

#print axioms bridge_hG1_slot_forces_surjective
#print axioms bridge_h310W_slot_unsatisfiable_at_witnessU

/-- **THE WRAPPER'S OWN BINDER LIST YIELDS `False` AT THE TREE'S ONE CONCRETE BACKGROUND.**

Stronger than `bridge_h310W_slot_unsatisfiable_at_witnessU`, and the same move
`BridgeRestricted.bridge_at_VReg_hypotheses_unsatisfiable` makes against its own construction: the
binders below are those of `bridge_at_measured_deltaPi` at `L := witnessL`, `U := witnessU` and the
unrestricted `W ≡ True`, and the unused `hreal` FEEDS the entire list to that theorem, forcing type
identity rather than a hand-copied lookalike. From the list alone, `False`.

`hγδ` gives `γ > deltaPiConst Jsup κ`, and `deltaPiConst Jsup κ ≥ 0` because `hJ` forces `Jsup ≥ 0`
and `hk0` gives `κ ≥ 0`; so `γ > 0`, and §12a's `h310W` collapse applies. -/
theorem bridge_at_measured_deltaPi_hypotheses_unsatisfiable_at_witnessU
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] [Nontrivial K]
    (J : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL →
      Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo) →
      PeriodicLatticeSite AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo)
    (DeltaPrimePi P : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL →
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
    (Q : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL → K)
    (Qstar : K → BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
    (G : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL →
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
    (T S : K →L[ℝ] K) (a γ q Jsup kappa : ℝ)
    (hadj : ∀ (x : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL) (B : K),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPiSym : ∀ u v : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hRiesz : ∀ A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
          (DeltaPrimePi (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm AdalyFormal.Balaban.CovariantOperators.witnessU J (Lam A) A)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) (hk0 : 0 ≤ kappa)
    (hlam : ∀ A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
      siteEnergy (Lam A) ≤ kappa ^ 2 * bondEnergy A)
    (hPpos : ∀ x : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
      (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
      (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hGW : ∀ B : K, (fun _ : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL => True)
      (G (Qstar B)))
    (hTdef : ∀ B : K, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
      AdalyFormal.Balaban.RecursiveBridge.fineMapOf
        (AdalyFormal.Balaban.RecursiveBridge.piExtendedMap
          (fun y => AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized
            AdalyFormal.Balaban.CovariantOperators.witnessU y) DeltaPrimePi)
        P Q Qstar a (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγδ : 0 < γ - deltaPiConst Jsup kappa) (hq : 0 < q) (ha : 0 ≤ a)
    (h310W : ∀ A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
      (fun _ : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL => True)
          (WithLp.toLp 2 A) →
      γ * ‖(WithLp.toLp 2 A : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ^ 2
        ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
            AdalyFormal.Balaban.CovariantOperators.witnessU A)
    (hQ : ∀ x : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL, ‖Q x‖ ≤ q * ‖x‖)
    (B : K) :
    False := by
  have hreal := bridge_at_measured_deltaPi
    (L := AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
    AdalyFormal.Balaban.CovariantOperators.witnessU J Lam DeltaPrimePi P
    (fun _ => True) Q Qstar G T S a γ q Jsup kappa
    hadj hPiSym hRiesz hJ hk0 hlam hPpos hPsym hGW hTdef hG1 hTS hγδ hq ha h310W hQ B
  clear hreal
  have hJ0 : 0 ≤ Jsup :=
    le_trans (frobNorm_nonneg _) (hJ (Classical.arbitrary
      (Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL)))
  have hd0 : 0 ≤ deltaPiConst Jsup kappa := by
    unfold deltaPiConst
    have : (0:ℝ) ≤ 28 + 48 * kappa := by linarith
    positivity
  exact bridge_h310W_slot_unsatisfiable_at_witnessU γ (by linarith) h310W

#print axioms bridge_at_measured_deltaPi_hypotheses_unsatisfiable_at_witnessU

/-! ## §13 — THE `α₀` THRESHOLD, EXPLICIT — AND WHAT A PINNED `κ` COSTS

`deltaPiConst` is LINEAR in `Jsup`, and §10 gives `Jsup ≤ 24·η⁻²·α₀`. So for every FINITE `κ` the
fixed-point criterion is met once the background is regular enough: `κ` RESCALES the admissible
`α₀`. `alphaThresholdPi` below is that rescaling, with must-fire and must-not-fire controls.

**⚠ FRAMING CORRECTED 2026-07-31 — both prosecutions convicted the previous sentence.**
~~"however large the gauge Green's-function bound `κ` turns out to be … `κ` RESCALES the admissible
`α₀`, it never obstructs it. That is the strongest statement available without an encoding of
`G'`"~~ — retained struck. Two things were wrong with it. **(i)** It read as a settled fact about the
actual construction while being conditional on `κ < ∞`, which nothing then proved. **(ii)** It is no
longer the strongest statement available: `KappaBound.lean` reaches `κ ≤ √768 = 16√3 ≈ 27.71`
(`KappaBound.hlam_at_kappa_sq_768`), and it does so **without ever encoding `G′`** — the operator is
eliminated structurally rather than constructed. So the honest reading of "rescales, never
obstructs" is now a NUMBER, not a reassurance: at `κ = √768` the admissible `α₀` is about `4·10⁻¹⁰`,
roughly `1/1250` of the tree's own `normAlpha`, and at `normAlpha` itself the criterion **fails**
(§9b, `criterion_fails_at_normAlpha_at_kappa_sqrt768`).

Two separate facts, kept separate: the admissible `α₀` sits BELOW `normAlpha` already at `κ = 1`
(`alphaThresholdPi_below_normAlpha_at_kappa_one`, a factor `≈2.43`), and `κ = √768` then costs a
FURTHER factor `495`–`496` (`deltaPiConst_kappa_ratio`). Only the second is `κ`'s doing.

The conditional `κ < ∞` is **not** discharged by that: `hlam_at_kappa_sq_768` carries four
hypotheses whose block-Poincaré input traces to an open `hblock`, read at the source and recorded in
§9b. What has changed is that the difficulty now has a candidate size and a named missing input,
instead of being unbounded and unnamed.

`G'`, `Q'`, `R` still have **no declaration anywhere in this tree** — re-measured at repair time,
zero hits in declaration position; the only occurrences are docstring prose. Their sole in-corpus
property remains CMP99b p.416 Theorem 3.11's *positivity*, asserted there with the words "This is
obvious for the first three operators" and therefore a DEFERRED claim this file does not build on
(LAW-12). `KappaBound`'s route does not build on it either — that is what makes the bound usable. -/

/-- The fixed-point criterion as an explicit THRESHOLD on `Jsup` (no existential). -/
theorem criterion_of_Jsup_le {γ₀ q Jsup kappa : ℝ} (hk : 0 < kappa)
    (hJ : Jsup ≤ γ₀ * (1 - q ^ 2) / (kappa * (28 + 48 * kappa))) :
    deltaPiConst Jsup kappa ≤ γ₀ * (1 - q ^ 2) := by
  have hden : 0 < kappa * (28 + 48 * kappa) := by nlinarith
  rw [le_div_iff₀ hden] at hJ
  unfold deltaPiConst
  calc Jsup * kappa * (28 + 48 * kappa) = Jsup * (kappa * (28 + 48 * kappa)) := by ring
    _ ≤ γ₀ * (1 - q ^ 2) := hJ

/-- **THE `α₀` THRESHOLD**, as a formula in the scale `η⁻²`, the gauge Green's-function bound `κ`,
the level-`0` coercivity `γ₀` and the blocking norm `q`. -/
noncomputable def alphaThresholdPi (etaInvSq kappa γ₀ q : ℝ) : ℝ :=
  γ₀ * (1 - q ^ 2) / (24 * etaInvSq * (kappa * (28 + 48 * kappa)))

/-- **THE ROUTE CLOSES BELOW THE THRESHOLD.** With `Jsup ≤ 24·η⁻²·α₀` (§10) and
`α₀ ≤ alphaThresholdPi η⁻² κ γ₀ q`, the iterated bridge keeps a positive uniform floor. -/
theorem uniformStepGamma_of_alpha_le {α₀ etaInvSq kappa γ₀ q : ℝ}
    (hα₀ : 0 ≤ α₀) (hη : 0 < etaInvSq) (hk : 0 < kappa) (hγ : 0 < γ₀)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hα : α₀ ≤ alphaThresholdPi etaInvSq kappa γ₀ q) :
    AdalyFormal.Balaban.GammaRecursion.UniformStepGamma
      (deltaPiConst (24 * etaInvSq * α₀) kappa) q := by
  have hden : 0 < kappa * (28 + 48 * kappa) := by nlinarith
  have hcoef : 0 < 24 * etaInvSq := by linarith
  have hJ : 24 * etaInvSq * α₀ ≤ γ₀ * (1 - q ^ 2) / (kappa * (28 + 48 * kappa)) := by
    unfold alphaThresholdPi at hα
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 24 * etaInvSq * (kappa * (28 + 48 * kappa)))] at hα
    rw [le_div_iff₀ hden]
    nlinarith [hα]
  exact uniformStepGamma_of_deltaPi hq0 hq1 hγ (criterion_of_Jsup_le hk hJ)

/-- **MUST-FIRE CONTROL.** At TWICE the threshold the criterion is strictly violated — so
`alphaThresholdPi` is the actual boundary and not a slack sufficient condition. -/
theorem criterion_fails_at_twice_threshold {etaInvSq kappa γ₀ q : ℝ}
    (hη : 0 < etaInvSq) (hk : 0 < kappa) (hγ : 0 < γ₀) (hq2 : q ^ 2 < 1) :
    γ₀ * (1 - q ^ 2)
      < deltaPiConst (24 * etaInvSq * (2 * alphaThresholdPi etaInvSq kappa γ₀ q)) kappa := by
  have hden : 0 < kappa * (28 + 48 * kappa) := by nlinarith
  have hne : (24 * etaInvSq * (kappa * (28 + 48 * kappa))) ≠ 0 := by positivity
  have hpos : 0 < γ₀ * (1 - q ^ 2) := by nlinarith
  have key : 24 * etaInvSq * (2 * alphaThresholdPi etaInvSq kappa γ₀ q) * kappa
      * (28 + 48 * kappa) = 2 * (γ₀ * (1 - q ^ 2)) := by
    unfold alphaThresholdPi
    field_simp
  unfold deltaPiConst
  rw [key]
  linarith

/-- **MUST-NOT-FIRE CONTROL.** The threshold is strictly positive at every admissible parameter, so
`uniformStepGamma_of_alpha_le` is never satisfied only by `α₀ = 0`. -/
theorem alphaThresholdPi_pos {etaInvSq kappa γ₀ q : ℝ}
    (hη : 0 < etaInvSq) (hk : 0 < kappa) (hγ : 0 < γ₀) (hq2 : q ^ 2 < 1) :
    0 < alphaThresholdPi etaInvSq kappa γ₀ q := by
  unfold alphaThresholdPi
  have h1 : (0 : ℝ) < 28 + 48 * kappa := by linarith
  have h2 : (0 : ℝ) < kappa * (28 + 48 * kappa) := mul_pos hk h1
  have h3 : (0 : ℝ) < 24 * etaInvSq := by linarith
  have hden : (0 : ℝ) < 24 * etaInvSq * (kappa * (28 + 48 * kappa)) := mul_pos h3 h2
  have hnum : (0 : ℝ) < γ₀ * (1 - q ^ 2) := mul_pos hγ (by linarith)
  exact div_pos hnum hden

/-- **THE THRESHOLD IS BELOW THE TREE'S OWN REGULARITY RADIUS ALREADY AT `κ = 1`.**
`alphaThresholdPi 1 1 normGamma (1/2) = 3/14592000 ≈ 2.06·10⁻⁷`, while `normAlpha = 5·10⁻⁷`. So the
admissible `α₀` was already a factor `≈2.43` below `normAlpha` before `κ` is taken into account at
all — the companion of §9b's `criterion_fails_at_normAlpha_at_kappa_one`, stated in `α₀` rather than
in `δ`. At `κ = √768` the threshold drops by a further factor `495`–`496`
(`deltaPiConst_kappa_ratio`), to `≈4.15·10⁻¹⁰`. -/
theorem alphaThresholdPi_below_normAlpha_at_kappa_one :
    alphaThresholdPi 1 1 AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma (1 / 2)
      < AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha := by
  unfold alphaThresholdPi AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
  norm_num

#print axioms criterion_of_Jsup_le
#print axioms uniformStepGamma_of_alpha_le
#print axioms criterion_fails_at_twice_threshold
#print axioms alphaThresholdPi_pos
#print axioms alphaThresholdPi_below_normAlpha_at_kappa_one

end AdalyFormal.Balaban.DeltaPrimeBound
