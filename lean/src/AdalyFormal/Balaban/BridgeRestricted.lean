/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.H310Satisfiability

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `BridgeRestricted.lean` — can the (3.10) hypothesis be RESTRICTED to the subspace?

## The question

`H310Satisfiability` proves the UNRESTRICTED (3.10) coercivity hypothesis unsatisfiable at every
background admitting an axis-compatible direction — including the flat one. The natural repair is
the one the bridge's own statement anticipates: `RecursiveBridge.bridge_from_fine_operator` demands
(3.10)-coercivity only on a subspace `W`, and the campaign has a PROVED restricted coercivity,
`CoercivityRegular.deltaKCLMNormalized_coercive_on_VReg`, on

  `VReg U = axial-gauge ∩ ker Q_2(U)`  (transported to `BondFnL2 L`).

**This module answers: that particular restriction cannot be used, and says exactly why, and then
supplies the repair that can.**

## §1–§2 — the naive restriction is IMPOSSIBLE, not merely unavailable

The bridge's own hypotheses `hGW`, `hT`, `hTS` FORCE `Q` to carry `W` ONTO `K`
(`bridge_witness_Q_eq`: `Q (G (Qstar (S B))) = B`, with `G (Qstar (S B))` in `W`). So any
`W ⊆ ker Q` makes the hypothesis set contradictory (`bridge_hyps_false_of_W_subset_kerQ`). And
`VReg U ⊆ ker (qCLM U 2)` **by construction** — the kernel clause is half of `VReg`'s definition
(`qCLM_eq_zero_of_mem_VReg`).

`bridge_at_VReg_hypotheses_unsatisfiable` takes the ENTIRE hypothesis list of
`RecursiveBridge.bridge_from_piExtended_normalized_threeTen` at `W := (· ∈ VReg U)` and the real
`Q`, feeds it to the real theorem (forcing type identity), and derives `False`.

This is a proved impossibility, in the same shape as `H310Satisfiability`'s. The irony is exact:
the `ker Q` clause is what excludes the null field that refutes the unrestricted hypothesis
(`dirConstField_not_mem_VReg_at_curvedRegularU`, §5), and it is the same clause that makes `W` unusable.

## §3 — what the bridge actually needs, and the repair that supplies it

The bridge needs a `W` TRANSVERSE to `ker Q`. The campaign has no coercivity there and this module
does not invent one. What it does instead is move the term that is already in (3.128) to where it
can do the work.

(3.128)'s fine operator is `M = Δ_π + P + Q*aQ`. `BridgeInverseAssembly.bridge_constructed` splits
it as (`Δ_π`, `P`, `a`) and demands `hDP : γ‖x‖² ≤ ⟨x,Δ_πx⟩ + ⟨x,Px⟩` — the `a`-term excluded from
the coercivity budget, because it is being saved to cancel `(3.156)`'s `−a⟨B,B⟩`.

`a • Q*Q` is symmetric and positive semidefinite. So it may be absorbed into `P`:

  `P' := P + a • (Q* ∘ Q)`,  `a' := 0`,  and `fineCLM Δ P' Q Q* 0 = fineCLM Δ P Q Q* a`
  (`fineCLM_absorb`, an operator identity — the FINE OPERATOR IS UNCHANGED).

Under that regrouping the coercivity demanded is the strictly weaker

  `hDPa : γ‖x‖² ≤ ⟨x,Δ_πx⟩ + ⟨x,Px⟩ + a‖Qx‖²`,

and the price is exactly the `−a‖B‖²` cancellation: the conclusion becomes `(γ/q²)‖B‖² ≤ ⟨B,SB⟩`
in place of `(γ/q²)‖B‖² ≤ ⟨B,SB⟩ − a‖B‖²`. Since `a ≥ 0` the new conclusion is WEAKER, and it is
stated as such. **A satisfiable instantiation proving less beats a vacuous one appearing to prove
more.**

## §4 — the `a`-augmented (3.10) input `h310a`, and ⚠ ITS REFUTATION IN §8

**⚠ CORRECTION, MADE IN THIS SAME PASS (S75), BEFORE THIS MODULE WAS EVER GRADED.** §4/§5 were
written to argue that `h310a` is the right replacement for the refuted unrestricted hypothesis.
§8 then tested that claim against my own construction and **REFUTED `h310a` ITSELF**. The struck
sentence below is retained so the reasoning that led there is visible; everything it asserts about
`h310a` being sufficient is WITHDRAWN. The individual theorems of §4/§5 are all still true — they
are just not enough.

Write `h310a A : γ₀‖A‖² ≤ deltaKQuadFormNormalizedCorrected U A + a‖Q A‖²` for the `a`-augmented
(3.10)-level statement.

* **On `ker Q` it is exactly the PROVED restricted coercivity.** The `a`-term vanishes there, so
  `h310a` restricted to `VReg U` IS `deltaKCLMNormalized_coercive_on_VReg`
  (`h310a_holds_on_VReg`, at `γ₀ := normGamma`, for every gauge-regular `U`). **STILL TRUE.**
* **The CONSTANT null field is carried by the `a`-term.** At `dirConstField d X` the whole of
  `h310a` reduces to `γ₀‖v‖² ≤ a‖Qv‖²` (`h310a_at_dirConstField_iff`), satisfiable precisely
  when `Q v ≠ 0`, and §5 proves `Q v ≠ 0` at `curvedRegularU`. **STILL TRUE.**

~~So the mechanism that refutes the unrestricted hypothesis does NOT refute `h310a`, and `h310a`
agrees with the campaign's proved coercivity on the subspace where that coercivity lives.~~
**SUPERSEDED BY §8.** A DIFFERENT mechanism does refute `h310a`: the ALTERNATING axis field is also
a null direction of `Δ_k`, and `Q` annihilates it. `H310A_false_at_curvedRegularU` proves
`¬ H310A curvedRegularU γ a` for every `γ > 0` and EVERY `a`. Consequently
`hDPa_of_source_chain` and `bridge_source_chain_a_augmented_at_curvedRegularU` — the two
declarations that route through `h310a` — have UNSATISFIABLE hypotheses
(`bridge_source_chain_a_augmented_hypotheses_unsatisfiable`, §9), exactly the defect this module
convicts elsewhere. §9 supplies the replacement that does not route through `h310a` and states
precisely what is left to prove.

## §5 — the null field is Q-VISIBLE at `curvedRegularU`

`curvedRegularU` is `rotElem 10⁻⁷` on one bond and `1` elsewhere. `rotM t = aI + bJ` with
`J = !![0,1;-1,0]`, and `J ∈ 𝔰𝔲(2)`; `J` commutes with `rotM t`, so `RMap (U b) J = J` for EVERY
bond (`curvedRegularU_linkFixes_rotGen`). A link-fixed `X` is transported trivially along every
path (`RMap_periodicPathHolonomy_of_linkFixed`, list induction), so the covariant block average of
`dirConstField d X` collapses to the flat one and evaluates to `X ≠ 0`
(`qCLM_dirConstField_ne_zero_at_curvedRegularU`).

Consequently `dirConstField d rotGen ∉ VReg curvedRegularU` (§5), and the `a`-term sees it.

## What is NOT claimed

* No coercivity of `Δ_k` off `ker Q` is proved here. ~~`h310a` is a HYPOTHESIS with a free `a`
  chosen by the consumer; what is proved is (i) it is not refuted by the mechanism that kills the
  unrestricted form, and (ii) it restricts on `VReg U` to a theorem.~~ **SUPERSEDED BY §8:
  `h310a` is FALSE.** What survives is `hDPa`, which keeps `⟨x,Px⟩`; §9 proves that the
  alternating field FORCES `P` itself to be coercive there, with constant `γ − δ`. That is the
  named residual this lane leaves, and it is a statement about the GAUGE-FIXING term, not about
  `Δ_k`.
* The regrouped chain's conclusion is WEAKER than the flagship's by the `−a‖B‖²` term. Stated in
  the theorem, not in prose only.
* This module edits nothing outside itself. No `sorry`. No new axiom.
-/

namespace AdalyFormal.Balaban.BridgeRestricted

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration periodicPathHolonomy periodicLatticeStep)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one RMap_mul_apply)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.H310Satisfiability (dirConstField dirConstField_dir AxisCompatible
  deltaKQuadFormNormalizedCorrected_dirConstField_eq_zero)

/-! ## §1 — THE STRUCTURAL FACT: the bridge forces `Q` to carry `W` ONTO `K`

Nothing here is about the lattice. These are the four hypotheses `hGW`, `hT`, `hTS` (plus
`Nontrivial K`) of `RecursiveBridge.bridge_from_fine_operator`, and nothing else. -/

section Abstract

variable {H K : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **The bridge's own hypotheses exhibit, for each `B : K`, a point of `W`.** No existential:
the point is `G (Qstar (S B))`, named. -/
theorem bridge_witness_mem_W (W : H → Prop) (Qstar : K → H) (G : H → H) (S : K →L[ℝ] K)
    (hGW : ∀ B : K, W (G (Qstar B))) (B : K) :
    W (G (Qstar (S B))) := hGW (S B)

/-- **And `Q` sends that point to `B`.** No existential. Together with `bridge_witness_mem_W` this
is the whole content of §1: `Q` carries `W` onto `K`. -/
theorem bridge_witness_Q_eq (Q : H → K) (Qstar : K → H) (G : H → H) (T S : K →L[ℝ] K)
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hTS : ∀ B : K, T (S B) = B) (B : K) :
    Q (G (Qstar (S B))) = B := by
  rw [← hT (S B), hTS B]

/-- The two together, as the surjectivity statement. The witness is CONSTRUCTED from the
hypotheses, not chosen: this is a consequence of the bridge's binders, not a free choice. -/
theorem bridge_forces_Q_onto_W (W : H → Prop) (Q : H → K) (Qstar : K → H) (G : H → H)
    (T S : K →L[ℝ] K)
    (hGW : ∀ B : K, W (G (Qstar B)))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hTS : ∀ B : K, T (S B) = B) (B : K) :
    ∃ x : H, W x ∧ Q x = B :=
  ⟨G (Qstar (S B)), bridge_witness_mem_W W Qstar G S hGW B,
    bridge_witness_Q_eq Q Qstar G T S hT hTS B⟩

/-- **THE NO-GO.** If `W` is contained in `ker Q`, the bridge's hypotheses `hGW`, `hT`, `hTS` are
contradictory on a nontrivial coarse carrier. No coercivity, symmetry, adjointness or `hG1`
hypothesis is used — three hypotheses suffice. -/
theorem bridge_hyps_false_of_W_subset_kerQ [Nontrivial K]
    (W : H → Prop) (Q : H → K) (Qstar : K → H) (G : H → H) (T S : K →L[ℝ] K)
    (hWker : ∀ x : H, W x → Q x = 0)
    (hGW : ∀ B : K, W (G (Qstar B)))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hTS : ∀ B : K, T (S B) = B) :
    False := by
  obtain ⟨B, hB⟩ := exists_ne (0 : K)
  refine hB ?_
  rw [← bridge_witness_Q_eq Q Qstar G T S hT hTS B]
  exact hWker _ (hGW (S B))

/-! ### §1b — CONTROLS on the no-go

Both directions, so the no-go is not vacuous bookkeeping. -/

/-- **MUST-NOT-FIRE (a): drop `hWker` and the remaining hypotheses ARE satisfiable.** `H = K = ℝ`,
`W ≡ True`, `Q = Qstar = G = T = S = id`. So `bridge_hyps_false_of_W_subset_kerQ` is not deriving
`False` from `hGW`/`hT`/`hTS` alone. -/
theorem no_go_must_not_fire_without_hWker :
    (∀ B : ℝ, (fun _ : ℝ => True) ((id : ℝ → ℝ) ((id : ℝ → ℝ) B)))
      ∧ (∀ B : ℝ, (ContinuousLinearMap.id ℝ ℝ) B = (id : ℝ → ℝ) ((id : ℝ → ℝ) ((id : ℝ → ℝ) B)))
      ∧ (∀ B : ℝ, (ContinuousLinearMap.id ℝ ℝ) ((ContinuousLinearMap.id ℝ ℝ) B) = B) :=
  ⟨fun _ => trivial, fun _ => rfl, fun _ => rfl⟩

/-- **MUST-NOT-FIRE (b): `Nontrivial K` is load-bearing.** On the trivial coarse carrier
`EuclideanSpace ℝ (Fin 0)` ALL FOUR hypotheses of the no-go hold simultaneously — with `Q = 0`, so
`hWker` holds too — and no contradiction follows, because there is no nonzero `B`. Hence the no-go
genuinely consumes `Nontrivial K`. -/
theorem no_go_must_not_fire_at_trivial_K :
    (∀ x : EuclideanSpace ℝ (Fin 0), (fun _ => True) x →
        (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : EuclideanSpace ℝ (Fin 0))) x = 0)
      ∧ (∀ B : EuclideanSpace ℝ (Fin 0), (fun _ => True)
          ((id : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) ((id : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) B)))
      ∧ (∀ B : EuclideanSpace ℝ (Fin 0),
          (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) B
            = (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : EuclideanSpace ℝ (Fin 0)))
                ((id : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0))
                  ((id : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) B)))
      ∧ (∀ B : EuclideanSpace ℝ (Fin 0),
          (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0))
            ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 0))) B) = B) := by
  refine ⟨fun _ _ => rfl, fun _ => trivial, fun _ => rfl, fun B => ?_⟩
  exact (Subsingleton.elim _ _)

end Abstract

/-! ## §2 — `VReg U ⊆ ker (qCLM U 2)`, and the bridge at `W := VReg` is contradictory -/

section VRegKernel

open AdalyFormal.Balaban.CoercivityRegular (VReg exists_of_mem_VReg admKerBare_ker)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply qRange)

variable {L : PeriodicLatticeExtent}

/-- **Half of `VReg`'s DEFINITION, made usable at the bridge's `Q`.** `VReg U` is
`axial ⊓ ker (lineCoarseRestrictCovLM U 2)` transported to `BondFnL2 L`, and `qCLM U 2` is the same
linear map transported the same way (`qCLM_apply` is `rfl`). -/
theorem qCLM_eq_zero_of_mem_VReg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {v : BondFnL2 L} (hv : v ∈ VReg U) :
    qCLM U 2 v = 0 := by
  obtain ⟨A, hA, hvA⟩ := exists_of_mem_VReg hv
  subst hvA
  have hpt : ∀ b : CoarseBond L 2,
      WithLp.ofLp (qCLM U 2 (WithLp.toLp 2 A : BondFnL2 L)) b = 0 := by
    intro b
    rw [qCLM_apply]
    exact admKerBare_ker hA b
  calc qCLM U 2 (WithLp.toLp 2 A : BondFnL2 L)
      = WithLp.toLp 2 (WithLp.ofLp (qCLM U 2 (WithLp.toLp 2 A : BondFnL2 L))) := rfl
    _ = WithLp.toLp 2 (fun _ : CoarseBond L 2 => (0 : SuTwo)) := by rw [funext hpt]
    _ = 0 := rfl

/-- The same at the corestricted `Q` the flagship actually uses. -/
theorem qRange_eq_zero_of_mem_VReg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {v : BondFnL2 L} (hv : v ∈ VReg U) :
    qRange (qCLM U 2) v = 0 :=
  Subtype.ext (qCLM_eq_zero_of_mem_VReg U hv)

end VRegKernel

/-! ## §3 — THE REPAIR: absorb `a • Q*Q` into `P`

`a • (Q* ∘ Q)` is symmetric and positive semidefinite whenever `a ≥ 0`, so it is a legitimate
summand of the `P` slot. Regrouping `(Δ, P, a) ↦ (Δ, P + a•Q*Q, 0)` leaves (3.128)'s FINE OPERATOR
UNCHANGED and weakens the coercivity demanded from `⟨x,Δx⟩+⟨x,Px⟩` to
`⟨x,Δx⟩+⟨x,Px⟩+a‖Qx‖²`. The price is the `−a‖B‖²` cancellation. -/

section Absorb

open AdalyFormal.Balaban.BridgeInverse (fineCLM fineCLM_apply fineCLM_inner)

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **`P' := P + a • Q*Q`.** -/
noncomputable def pAbsorb (P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ) :
    H →L[ℝ] H :=
  P + a • (Qstar.comp Q)

/-- **THE FINE OPERATOR IS UNCHANGED.** `Δ + P' + 0·Q*Q = Δ + P + a·Q*Q`, as operators. This is
what makes the regrouping a bookkeeping move on (3.128) rather than a change of object. -/
theorem fineCLM_absorb (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ) :
    fineCLM Delta (pAbsorb P Q Qstar a) Q Qstar 0 = fineCLM Delta P Q Qstar a := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  rw [fineCLM_apply, fineCLM_apply]
  show Delta x + (P x + a • Qstar (Q x)) + (0 : ℝ) • Qstar (Q x)
      = Delta x + P x + a • Qstar (Q x)
  rw [zero_smul, add_zero, add_assoc]

/-- The diagonal of `P'`. -/
theorem pAbsorb_inner (P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ)) (x : H) :
    (inner ℝ x (pAbsorb P Q Qstar a x) : ℝ) = (inner ℝ x (P x) : ℝ) + a * ‖Q x‖ ^ 2 := by
  have h1 : (inner ℝ x (Qstar (Q x)) : ℝ) = ‖Q x‖ ^ 2 := by
    have h2 : (inner ℝ (Qstar (Q x)) x : ℝ) = ‖Q x‖ ^ 2 := by
      rw [hadj x (Q x), real_inner_self_eq_norm_sq]
    rw [← h2]
    exact real_inner_comm _ _
  show (inner ℝ x (P x + a • Qstar (Q x)) : ℝ) = _
  rw [inner_add_right, real_inner_smul_right, h1]

/-- `P'` is symmetric when `P` is. -/
theorem pAbsorb_symm (P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPsym : ∀ u v : H, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ)) (u v : H) :
    (inner ℝ u (pAbsorb P Q Qstar a v) : ℝ) = (inner ℝ (pAbsorb P Q Qstar a u) v : ℝ) := by
  have e1 : (inner ℝ u (Qstar (Q v)) : ℝ) = (inner ℝ (Q v) (Q u) : ℝ) := by
    rw [← hadj u (Q v)]
    exact real_inner_comm _ _
  have e2 : (inner ℝ (Qstar (Q u)) v : ℝ) = (inner ℝ (Q u) (Q v) : ℝ) := hadj v (Q u)
  show (inner ℝ u (P v + a • Qstar (Q v)) : ℝ) = (inner ℝ (P u + a • Qstar (Q u)) v : ℝ)
  rw [inner_add_right, inner_add_left, real_inner_smul_right, real_inner_smul_left,
    hPsym u v, e1, e2, real_inner_comm (Q v) (Q u)]

/-- `P'` is positive semidefinite when `P` is and `a ≥ 0`. -/
theorem pAbsorb_pos (P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ)) (ha : 0 ≤ a) (x : H) :
    (0 : ℝ) ≤ (inner ℝ x (pAbsorb P Q Qstar a x) : ℝ) := by
  rw [pAbsorb_inner P Q Qstar a hadj x]
  have h2 : (0 : ℝ) ≤ a * ‖Q x‖ ^ 2 := by positivity
  linarith [hPpos x]

/-- **The `a`-augmented coercivity IS the ordinary coercivity of `(Δ, P')`.** This is the exact
translation step: `hDPa` in, `bridge_constructed`'s `hDP` out. -/
theorem hDP_pAbsorb_of_hDPa (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDPa : ∀ x : H, γ * ‖x‖ ^ 2
      ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) + a * ‖Q x‖ ^ 2) (x : H) :
    γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (pAbsorb P Q Qstar a x) : ℝ) := by
  rw [pAbsorb_inner P Q Qstar a hadj x]
  linarith [hDPa x]

end Absorb

/-! ### §3b — the regrouped constructed bridge

`bridge_constructed` verbatim, run on `(Δ, P', 0)`. The conclusion carries `− 0 * ‖B‖²`, i.e. the
`a`-cancellation is GONE: this is strictly weaker than
`BridgeInverseAssembly.bridge_constructed`'s conclusion at the same `γ`, `q`, and that weakening is
the whole price of the repair. -/

section AbsorbedBridge

open AdalyFormal.Balaban.BridgeInverse (fineCLM bridge_constructed sOp
  qstar_injective_of_surjective)

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- **THE REGROUPED BRIDGE.** Input: the `a`-augmented coercivity `hDPa`. Output: the source-free
coarse bound WITHOUT the `−a‖B‖²` term.

Compare `BridgeInverseAssembly.bridge_constructed`, whose input is the strictly stronger
`γ‖x‖² ≤ ⟨x,Δx⟩+⟨x,Px⟩` and whose output carries `− a‖B‖²`. The operator inverted is the SAME
(`fineCLM_absorb`). -/
theorem bridge_constructed_a_absorbed
    (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ q : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDsym : ∀ u v : H, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : H, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγ : 0 < γ) (hq : 0 < q)
    (hDPa : ∀ x : H, γ * ‖x‖ ^ 2
      ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) + a * ‖Q x‖ ^ 2)
    (hQsurj : Function.Surjective Q)
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp Delta (pAbsorb P Q Qstar a) Q Qstar 0 γ hadj hγ le_rfl
            (hDP_pAbsorb_of_hDPa Delta P Q Qstar a γ hadj hDPa)
            (qstar_injective_of_surjective Q Qstar hadj hQsurj) B) : ℝ) := by
  have h := bridge_constructed Delta (pAbsorb P Q Qstar a) Q Qstar 0 γ q hadj hDsym
    (pAbsorb_symm P Q Qstar a hadj hPsym) hγ hq le_rfl
    (hDP_pAbsorb_of_hDPa Delta P Q Qstar a γ hadj hDPa) hQsurj hQ B
  simpa using h

end AbsorbedBridge

/-! ## §4 — THE (3.10)-LEVEL INPUT `h310a`, and its two halves -/

section H310a

open AdalyFormal.Balaban.CoercivityRegular (VReg deltaKCLMNormalized_coercive_on_VReg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular)
open AdalyFormal.Balaban.LemmaAssemblyNormalized (normAlpha normGamma normGamma_pos)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.BridgeInverse (qCLM)

variable {L : PeriodicLatticeExtent}

/-- **`h310a` — the (3.10)-level hypothesis of the regrouped chain**: (3.10)'s quadratic form PLUS
the block-average term `a‖Q A‖²` that (3.128) already contains. -/
def H310A (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (γ a : ℝ) : Prop :=
  ∀ A : Bond L → SuTwo,
    γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2
      ≤ deltaKQuadFormNormalizedCorrected U A
        + a * ‖qCLM U 2 (WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2

/-- **HALF ONE — on `ker Q` the `a`-term vanishes and `h310a` IS the campaign's PROVED restricted
coercivity.** `deltaKCLMNormalized_coercive_on_VReg`, verbatim, at `γ := normGamma = 1/2000`. No
new mathematics: this records that `h310a` and the proved result AGREE where the proved result
lives. -/
theorem h310a_holds_on_VReg (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular normAlpha U) (a : ℝ)
    (A : Bond L → SuTwo) (hA : (WithLp.toLp 2 A : BondFnL2 L) ∈ VReg U) :
    normGamma * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2
      ≤ deltaKQuadFormNormalizedCorrected U A
        + a * ‖qCLM U 2 (WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 := by
  have hz : qCLM U 2 (WithLp.toLp 2 A : BondFnL2 L) = 0 := qCLM_eq_zero_of_mem_VReg U hA
  rw [hz, norm_zero]
  have hcoerc := deltaKCLMNormalized_coercive_on_VReg hL hdvd U hreg
    (WithLp.toLp 2 A : BondFnL2 L) hA
  rw [inner_deltaKCLMNormalized_eq U A] at hcoerc
  simpa using hcoerc

/-- **HALF TWO — at the null field, `h310a` reduces EXACTLY to `γ‖v‖² ≤ a‖Qv‖²`.** The whole of
`Δ_k`'s contribution is `0` there (`H310Satisfiability`), so the null field constrains `h310a`
ONLY through `Q`. It refutes `h310a` iff `Q v = 0`, and it does not otherwise. -/
theorem h310a_at_dirConstField_iff
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X) (γ a : ℝ) :
    (γ * ‖(WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2
        ≤ deltaKQuadFormNormalizedCorrected U (dirConstField d X)
          + a * ‖qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2)
      ↔ (γ * ‖(WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2
        ≤ a * ‖qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2) := by
  rw [deltaKQuadFormNormalizedCorrected_dirConstField_eq_zero U d X hax, zero_add]

/-- **The explicit `a` that makes the null field satisfy the `a`-augmented inequality**, given only
that `Q` sees the field. No existential: `a` is written down. This is the precise sense in which
`H310Satisfiability`'s refutation DOES NOT TRANSFER. -/
theorem dirConstField_satisfies_h310a_at
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X) (γ : ℝ)
    (hQ : qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L) ≠ 0) :
    γ * ‖(WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2
      ≤ deltaKQuadFormNormalizedCorrected U (dirConstField d X)
        + (γ * ‖(WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2
            / ‖qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2)
          * ‖qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2 := by
  rw [(h310a_at_dirConstField_iff U d X hax γ _)]
  have hn : ‖qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2 ≠ 0 := by
    have : ‖qCLM U 2 (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ≠ 0 :=
      norm_ne_zero_iff.2 hQ
    positivity
  rw [div_mul_cancel₀ _ hn]

end H310a

/-! ## §5 — THE NULL FIELD IS `Q`-VISIBLE

The whole of §4's half two turns on `Q v ≠ 0` at the null field. This section proves it at
`curvedRegularU`, the flagship's own background.

The route avoids all path combinatorics: pick `X` FIXED BY EVERY LINK. Then every covariant
transport in `Q`'s definition acts as the identity on `X`, the covariant block average of
`dirConstField d X` collapses to the flat one, and the flat one is a TRUE AVERAGE of a constant. -/

section LinkFixedTransport

open AdalyFormal.Balaban.CovariantOperators (RMap_coe_apply suTwo)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply)

variable {L : PeriodicLatticeExtent}

/-- **`X` is fixed by the adjoint action of EVERY link of `U`.** Strictly stronger than
`H310Satisfiability.AxisCompatible`, which excuses the bonds of direction `d`. -/
def LinkFixed (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (X : SuTwo) : Prop :=
  ∀ b : Bond L, RMap (U b) X = X

/-- Link-fixed implies axis-compatible in EVERY direction, so §4's null-field lemmas apply. -/
theorem axisCompatible_of_linkFixed
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (X : SuTwo) (h : LinkFixed U X) (d : Fin 3) : AxisCompatible U d X :=
  fun b _ => h b

/-- A fixed vector of `RMap g` is fixed by `RMap g⁻¹`. -/
theorem RMap_inv_of_fixed (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo)
    (h : RMap g X = X) : RMap g⁻¹ X = X := by
  conv_lhs => rw [← h]
  rw [RMap_mul_apply, inv_mul_cancel, RMap_one]
  rfl

/-- **Trivial transport along EVERY path.** List induction on the signed path; each factor is a
link value or its inverse, and both fix `X`. -/
theorem RMap_periodicPathHolonomy_of_linkFixed
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (X : SuTwo) (h : LinkFixed U X) :
    ∀ (p : List (Fin 3 × Bool)) (x : PeriodicLatticeSite L),
      RMap (periodicPathHolonomy U x p) X = X := by
  intro p
  induction p with
  | nil =>
      intro x
      show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) X = X
      rw [RMap_one]
      rfl
  | cons step rest ih =>
      intro x
      show RMap ((if step.2 then U (x, step.1)
          else (U (periodicLatticeStep x step, step.1))⁻¹)
          * periodicPathHolonomy U (periodicLatticeStep x step) rest) X = X
      rw [← RMap_mul_apply, ih (periodicLatticeStep x step)]
      by_cases hs : step.2 = true
      · rw [if_pos hs]
        exact h _
      · rw [if_neg hs]
        exact RMap_inv_of_fixed _ _ (h _)

/-- **`rZeroA` on the null field, at a coarse bond of direction `d`.** Every one of the `ell`
transported summands is `X`. -/
theorem rZeroA_dirConstField
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (h : LinkFixed U X)
    (cMinus x : PeriodicLatticeSite L) (μ : Fin 3) (hμ : μ = d) (ell : ℕ) :
    rZeroA U cMinus x (dirConstField d X) μ ell = ell • X := by
  have hterm : ∀ i ∈ Finset.range ell,
      RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ i))
        (dirConstField d X (pathSite x μ i, μ)) = X := by
    intro i _
    rw [dirConstField_dir, if_pos hμ]
    exact RMap_periodicPathHolonomy_of_linkFixed U X h _ _
  show (∑ i ∈ Finset.range ell,
      RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ i))
        (dirConstField d X (pathSite x μ i, μ))) = ell • X
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]

/-- **`Q` on the null field, EXACTLY**, at any coarse bond of direction `d`, over any link-fixed
`X`. The value is a positive rational multiple of `X` — in particular nonzero. -/
theorem lineCoarseRestrictCov_dirConstField
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (h : LinkFixed U X) (ell : ℕ) (b : CoarseBond L ell)
    (hb : b.2 = d) :
    lineCoarseRestrictCov U ell (dirConstField d X) b
      = ((((blockOf b.1.1 ell).card * ell : ℕ) : ℝ) / (ell : ℝ) ^ 4) • X := by
  show (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell,
      rZeroA U b.1.1 x (dirConstField d X) b.2 ell = _
  rw [Finset.sum_congr rfl
      (fun x _ => rZeroA_dirConstField U d X h b.1.1 x b.2 hb ell),
    Finset.sum_const, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ ((blockOf b.1.1 ell).card * ell) X, smul_smul]
  congr 1
  rw [one_div, inv_mul_eq_div]

/-- **THE `Q`-VISIBILITY, general.** At any background with a link-fixed nonzero `X`, on any
extent, at any coarse bond of direction `d` with a nonempty block and `ell > 0`, the null field has
nonzero block average. -/
theorem qCLM_dirConstField_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (h : LinkFixed U X) (hX : X ≠ 0) (ell : ℕ) (hell : 0 < ell)
    (b : CoarseBond L ell) (hb : b.2 = d) (hcard : 0 < (blockOf b.1.1 ell).card) :
    qCLM U ell (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L) ≠ 0 := by
  intro hcon
  have h0 : WithLp.ofLp
      (qCLM U ell (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)) b = 0 := by
    rw [hcon]; rfl
  rw [qCLM_apply, show WithLp.ofLp (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)
      = dirConstField (L := L) d X from rfl,
    lineCoarseRestrictCov_dirConstField U d X h ell b hb] at h0
  have hne : ((((blockOf b.1.1 ell).card * ell : ℕ) : ℝ) / (ell : ℝ) ^ 4) ≠ 0 := by
    have h1 : ((blockOf b.1.1 ell).card * ell : ℕ) ≠ 0 := by positivity
    have h2 : ((((blockOf b.1.1 ell).card * ell : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 h1
    have h3 : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hell.ne'
    exact div_ne_zero h2 (by positivity)
  rcases smul_eq_zero.1 h0 with hc | hc
  · exact hne hc
  · exact hX hc

end LinkFixedTransport

/-! ### §5b — a link-fixed nonzero element at `curvedRegularU`

`rotM t = a(t)·I + b(t)·J` with `J = !![0,1;-1,0]`. `J` is real antisymmetric, hence anti-Hermitian
and traceless, so `J ∈ 𝔰𝔲(2)`; and `J` commutes with `rotM t` because `rotM t` lies in the
commutative algebra `ℝ·I ⊕ ℝ·J`. So `RMap (rotElem t) J = J` for every `t`, and since
`curvedRegularU` is `1` off its single active bond, `J` is fixed by EVERY link. -/

section RotGen

open AdalyFormal.Balaban.CovariantOperators (RMap_coe_apply suTwo)
open AdalyFormal.Balaban.NonFlatBackground (rotElem rotM rotA rotB rotM_conjTranspose
  rotA_sq_add_rotB_sq_complex)

/-- `J = !![0,1;-1,0]`, the generator of the rotation family. -/
def rotGenVal : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem rotGenVal_mem : rotGenVal ∈ suTwo := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rotGenVal, Matrix.conjTranspose_apply]
  · simp [rotGenVal, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- `J`, as an element of `𝔰𝔲(2)`. -/
def rotGen : SuTwo := ⟨rotGenVal, rotGenVal_mem⟩

theorem rotGenVal_ne_zero : rotGenVal ≠ 0 := by
  intro h
  have h01 : rotGenVal 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by rw [h]
  simp [rotGenVal] at h01

theorem rotGen_ne_zero : rotGen ≠ 0 := fun h => rotGenVal_ne_zero (congrArg Subtype.val h)

/-- **`RMap (rotElem t) J = J`, for every `t`.** Explicit `2×2` computation; the only input is
`a(t)² + b(t)² = 1`. -/
theorem RMap_rotElem_rotGen (t : ℝ) : RMap (rotElem t) rotGen = rotGen := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  show (rotM t) * rotGenVal * (rotM t).conjTranspose = rotGenVal
  rw [rotM_conjTranspose]
  have hab := rotA_sq_add_rotB_sq_complex t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, rotGenVal, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | ring1
      | linear_combination hab
      | linear_combination -hab

end RotGen

/-! ### §5c — the two consequences at `curvedRegularU` -/

section CurvedRegular

open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU VReg curvedT)
open AdalyFormal.Balaban.RegularUCurvedWitness (curvedBond curvedBond_dir bondU bondU_at bondU_off
  curvedFamilyU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.BridgeInverse (qCLM siteZeroMem)
open AdalyFormal.Balaban.NonFlatBackground (rotElem)

/-- **`rotGen` is fixed by EVERY link of `curvedRegularU`.** -/
theorem curvedRegularU_linkFixes_rotGen : LinkFixed curvedRegularU rotGen := by
  intro b
  by_cases hb : b = curvedBond
  · have hU : curvedRegularU b = rotElem curvedT := by
      rw [hb]; exact bondU_at curvedBond (rotElem curvedT)
    rw [hU]
    exact RMap_rotElem_rotGen curvedT
  · have hU : curvedRegularU b = 1 := bondU_off curvedBond (rotElem curvedT) hb
    rw [hU, RMap_one]
    rfl

/-- The coarse bond used below: base site `0`, direction `0` — the direction of `curvedBond`. -/
def zeroCoarseBond : CoarseBond witL5 2 :=
  (⟨(fun _ => 0 : PeriodicLatticeSite witL5), siteZeroMem witL5 2⟩, 0)

theorem zeroCoarseBond_dir : zeroCoarseBond.2 = (0 : Fin 3) := rfl

/-- The block of the zero site is nonempty — it contains the zero site. -/
theorem zeroCoarseBond_block_card_pos :
    0 < (blockOf zeroCoarseBond.1.1 2).card :=
  Finset.card_pos.mpr ⟨(fun _ => 0 : PeriodicLatticeSite witL5),
    mem_blockOf.mpr (by decide)⟩

/-- **THE `Q`-VISIBILITY AT `curvedRegularU`.** The null field of `Δ_k` at direction `0` — the very
field that refutes the unrestricted (3.10) hypothesis at this background — has NONZERO block
average. So the `a`-term of (3.128) sees exactly the direction `Δ_k` is blind to. -/
theorem qCLM_dirConstField_ne_zero_at_curvedRegularU :
    qCLM curvedRegularU 2
        (WithLp.toLp 2 (dirConstField (L := witL5) (0 : Fin 3) rotGen) : BondFnL2 witL5) ≠ 0 :=
  qCLM_dirConstField_ne_zero curvedRegularU (0 : Fin 3) rotGen curvedRegularU_linkFixes_rotGen
    rotGen_ne_zero 2 (by norm_num) zeroCoarseBond zeroCoarseBond_dir
    zeroCoarseBond_block_card_pos

/-- **THE NULL FIELD IS EXCLUDED BY THE RESTRICTION — via the `ker Q` clause.** This answers the
"does `W` remove the offending direction?" question affirmatively, and simultaneously identifies
the clause that does the removing as exactly the one §1–§2 prove unusable. -/
theorem dirConstField_not_mem_VReg_at_curvedRegularU :
    (WithLp.toLp 2 (dirConstField (L := witL5) (0 : Fin 3) rotGen) : BondFnL2 witL5)
      ∉ VReg curvedRegularU := by
  intro hmem
  exact qCLM_dirConstField_ne_zero_at_curvedRegularU (qCLM_eq_zero_of_mem_VReg curvedRegularU hmem)

/-- **THE REFUTATION DOES NOT TRANSFER, at `curvedRegularU`, with the constant written down.**
The unrestricted (3.10) hypothesis is FALSE at this background for every `γ > 0`
(`H310Satisfiability.h310_unrestricted_impossible_at_curvedRegularU`). Its `a`-augmented
counterpart is SATISFIED at the same field, at the same `γ`, for the explicit `a` below. -/
theorem dirConstField_satisfies_h310a_at_curvedRegularU (γ : ℝ) :
    γ * ‖(WithLp.toLp 2 (dirConstField (L := witL5) (0 : Fin 3) rotGen) : BondFnL2 witL5)‖ ^ 2
      ≤ deltaKQuadFormNormalizedCorrected curvedRegularU (dirConstField (0 : Fin 3) rotGen)
        + (γ * ‖(WithLp.toLp 2 (dirConstField (L := witL5) (0 : Fin 3) rotGen) :
              BondFnL2 witL5)‖ ^ 2
            / ‖qCLM curvedRegularU 2 (WithLp.toLp 2 (dirConstField (L := witL5) (0 : Fin 3) rotGen) :
              BondFnL2 witL5)‖ ^ 2)
          * ‖qCLM curvedRegularU 2 (WithLp.toLp 2 (dirConstField (L := witL5) (0 : Fin 3) rotGen) :
              BondFnL2 witL5)‖ ^ 2 :=
  dirConstField_satisfies_h310a_at curvedRegularU (0 : Fin 3) rotGen
    (axisCompatible_of_linkFixed curvedRegularU rotGen curvedRegularU_linkFixes_rotGen (0 : Fin 3))
    γ qCLM_dirConstField_ne_zero_at_curvedRegularU

end CurvedRegular

/-! ## §6 — THE TWO PUNCHLINES

**(a)** the generic consumer's binders at `W := VReg U` are contradictory (a proved impossibility
for the naive restriction), and **(b)** the `curvedRegularU` chain, re-run on the `a`-augmented
(3.10) input, with the weaker conclusion stated. -/

section Punchlines

open AdalyFormal.Balaban.CoercivityRegular (VReg curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.RecursiveBridge (fineMapOf piExtendedMap
  bridge_from_piExtended_normalized_threeTen)
open AdalyFormal.Balaban.BridgeInverse (qCLM CoarseFnL2 qRange qRangeStar qRange_hadj qRange_le
  qRange_surjective piCLM piCLM_apply piCLM_symm qCLM_norm_pos nontrivial_range_curved
  witL5_dvd_two witL5_wide_two sOp qstar_injective_of_surjective)

variable {L : PeriodicLatticeExtent}

/-! ### §6a — the generic consumer at `W := VReg U` -/

/-- **THE GENERIC BRIDGE'S OWN HYPOTHESIS LIST AT `W := (· ∈ VReg U)` IS CONTRADICTORY.**

Every binder below is character-for-character a binder of
`RecursiveBridge.bridge_from_piExtended_normalized_threeTen` with `W := (· ∈ VReg U)`, and the
unused `hreal` FEEDS them to that theorem — so if any type differed this file would not compile.
The `False` then comes from three of them (`hGW`, `hT`, `hTS`) plus `hWker`.

`hWker` is a hypothesis here only so that the statement is about `Q` in general; it is DISCHARGED
by `qCLM_eq_zero_of_mem_VReg` at the real `Q` (see `bridge_at_VReg_unsatisfiable_at_realQ`). -/
theorem bridge_at_VReg_hypotheses_unsatisfiable
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] [Nontrivial K]
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi P : BondFnL2 L → BondFnL2 L)
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (T S : K →L[ℝ] K) (a γ δ q : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hpi : ∀ x : BondFnL2 L, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hGW : ∀ B : K, (fun v : BondFnL2 L => v ∈ VReg U) (G (Qstar B)))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 L,
      fineMapOf (piExtendedMap (fun y => deltaKCLMNormalized U y) DeltaPrimePi) P Q Qstar a (G x)
        = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγδ : 0 < γ - δ) (hq : 0 < q) (ha : 0 ≤ a)
    (h310W : ∀ A : Bond L → SuTwo, (fun v : BondFnL2 L => v ∈ VReg U) (WithLp.toLp 2 A) →
      γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 ≤ deltaKQuadFormNormalizedCorrected U A)
    (hQ : ∀ x : BondFnL2 L, ‖Q x‖ ≤ q * ‖x‖) (B : K)
    (hWker : ∀ v : BondFnL2 L, v ∈ VReg U → Q v = 0) :
    False := by
  have hreal := bridge_from_piExtended_normalized_threeTen U DeltaPrimePi P
    (fun v : BondFnL2 L => v ∈ VReg U) Q Qstar G T S a γ δ q hadj hPiSym hpi hPpos hPsym
    hGW hT hG1 hTS hγδ hq ha h310W hQ B
  clear hreal
  exact bridge_hyps_false_of_W_subset_kerQ (fun v : BondFnL2 L => v ∈ VReg U) Q Qstar G T S
    hWker hGW hT hTS

/-- **AND AT THE REAL `Q`, `hWker` IS A THEOREM.** Only the three hypotheses that carry the
contradiction are listed; the rest are irrelevant to it and are not stated, so there is no doubt
about which binders are doing the work. `Q := qRange (qCLM U 2)` is the flagship's own `Q`. -/
theorem bridge_at_VReg_unsatisfiable_at_realQ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [Nontrivial (LinearMap.range (qCLM U 2 : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L 2))]
    (Qstar : (LinearMap.range (qCLM U 2 : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L 2)) → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L)
    (T S : (LinearMap.range (qCLM U 2 : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L 2)) →L[ℝ]
      (LinearMap.range (qCLM U 2 : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L 2)))
    (hGW : ∀ B, G (Qstar B) ∈ VReg U)
    (hT : ∀ B, T B = qRange (qCLM U 2) (G (Qstar B)))
    (hTS : ∀ B, T (S B) = B) :
    False :=
  bridge_hyps_false_of_W_subset_kerQ (fun v : BondFnL2 L => v ∈ VReg U)
    (fun x => qRange (qCLM U 2) x) Qstar G T S
    (fun v hv => qRange_eq_zero_of_mem_VReg U hv) hGW hT hTS

/-- The same, at the flagship's own background, with `Nontrivial` discharged
(`nontrivial_range_curved`). -/
theorem bridge_at_VReg_unsatisfiable_at_curvedRegularU
    (Qstar : (LinearMap.range (qCLM curvedRegularU 2 :
      BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2)) → BondFnL2 witL5)
    (G : BondFnL2 witL5 → BondFnL2 witL5)
    (T S : (LinearMap.range (qCLM curvedRegularU 2 :
        BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2)) →L[ℝ]
      (LinearMap.range (qCLM curvedRegularU 2 :
        BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2)))
    (hGW : ∀ B, G (Qstar B) ∈ VReg curvedRegularU)
    (hT : ∀ B, T B = qRange (qCLM curvedRegularU 2) (G (Qstar B)))
    (hTS : ∀ B, T (S B) = B) :
    False :=
  letI := nontrivial_range_curved
  bridge_at_VReg_unsatisfiable_at_realQ curvedRegularU Qstar G T S hGW hT hTS

/-! ### §6b — the `curvedRegularU` chain on the `a`-augmented (3.10) input -/

/-- The corestriction does not change the norm. -/
theorem norm_qRange_eq {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : BondFnL2 L) : ‖qRange (qCLM U ell) x‖ = ‖qCLM U ell x‖ := rfl

/-- **⚠ DEAD ROUTE (S75, same pass). `hDPa` FROM `h310a`** — the `a`-augmented analogue of
`BridgeInverse.hDP_of_source_chain`. Same `hpi` (p.419's deferred two-sided bound), same `hPpos`;
the ONLY change is that the (3.10)-level input carries the `a‖QA‖²` term.

**The theorem is TRUE; its hypothesis `h310a` is UNSATISFIABLE** at `curvedRegularU`
(`H310A_false_at_curvedRegularU`, §8). Retained because it is the honest record of the route
attempted, and because `H310A` must exist as a named object for §8 to refute it. **Do not consume
it.** Use `bridge_constructed_a_absorbed` with `hDPa` supplied directly — see
`bridge_source_chain_hDPa_at_curvedRegularU` (§9). -/
theorem hDPa_of_source_chain
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ₀ δ : ℝ)
    (h310a : H310A U γ₀ a)
    (hpi : ∀ x : BondFnL2 L, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ)) (x : BondFnL2 L) :
    (γ₀ - δ) * ‖x‖ ^ 2
      ≤ (inner ℝ x (piCLM U DeltaPrimePi x) : ℝ) + (inner ℝ x (P x) : ℝ)
        + a * ‖qRange (qCLM U 2) x‖ ^ 2 := by
  have hx : (WithLp.toLp 2 (WithLp.ofLp x) : BondFnL2 L) = x := rfl
  have h1 := h310a (WithLp.ofLp x)
  rw [hx] at h1
  have hform : (inner ℝ x (deltaKCLMNormalized U x) : ℝ)
      = deltaKQuadFormNormalizedCorrected U (WithLp.ofLp x) := by
    rw [← inner_deltaKCLMNormalized_eq U (WithLp.ofLp x), hx]
  rw [← hform] at h1
  rw [piCLM_apply, inner_sub_right, norm_qRange_eq]
  have h2 : (inner ℝ x (DeltaPrimePi x) : ℝ) ≤ δ * ‖x‖ ^ 2 := le_trans (le_abs_self _) (hpi x)
  have h3 := hPpos x
  nlinarith [h1, h2, h3]

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
/-- **⚠ VACUOUS (S75, same pass) — RETAINED AS THE RECORD OF THE ATTEMPT.
THE SOURCE CHAIN AT `curvedRegularU`, ON THE `a`-AUGMENTED (3.10) INPUT.**

Its `h310a` binder is proved unsatisfiable in §8, so this theorem proves nothing about
`curvedRegularU`; `bridge_source_chain_a_augmented_hypotheses_unsatisfiable` (§9) states that in
the tree, in the same shape `H310Satisfiability` uses. The live replacement is
`bridge_source_chain_hDPa_at_curvedRegularU` (§9), which takes `hDPa` directly.

Everything `BridgeInverse.bridge_source_chain_at_curvedRegularU` constructs is still constructed:
`Q` is the faithful covariant block average at `curvedRegularU`, `Q*` its adjoint, `G₁` and `S` are
built (through `sOp`), and `hG1`/`hTS` are theorems. The FINE OPERATOR INVERTED IS THE SAME
`Δ_π + P + Q*aQ` (`fineCLM_absorb`).

Two things differ from the flagship, and both are in the statement:

* the (3.10)-level input is `h310a` (`H310A curvedRegularU γ₀ a`) instead of the unrestricted
  `h310` that `H310Satisfiability` proves unsatisfiable;
* the conclusion has NO `− a‖B‖²` term. That is the price of the regrouping and it makes the
  conclusion weaker than the flagship's at the same `γ₀, δ, q`. -/
theorem bridge_source_chain_a_augmented_at_curvedRegularU
    (DeltaPrimePi P : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (a γ₀ δ : ℝ)
    (hPiSym : ∀ u v : BondFnL2 witL5,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 witL5, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγδ : 0 < γ₀ - δ)
    (h310a : H310A curvedRegularU γ₀ a)
    (hpi : ∀ x : BondFnL2 witL5, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 witL5, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (B : (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2))) :
    ((γ₀ - δ) / ‖qCLM curvedRegularU 2‖ ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp (piCLM curvedRegularU DeltaPrimePi)
            (pAbsorb P (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a)
            (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) 0 (γ₀ - δ)
            (qRange_hadj curvedRegularU) hγδ le_rfl
            (hDP_pAbsorb_of_hDPa (piCLM curvedRegularU DeltaPrimePi) P
              (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a (γ₀ - δ)
              (qRange_hadj curvedRegularU)
              (hDPa_of_source_chain curvedRegularU DeltaPrimePi P a γ₀ δ h310a hpi hPpos))
            (qstar_injective_of_surjective _ _ (qRange_hadj curvedRegularU)
              (qRange_surjective (qCLM curvedRegularU 2))) B) : ℝ) :=
  letI := nontrivial_range_curved
  bridge_constructed_a_absorbed (piCLM curvedRegularU DeltaPrimePi) P
    (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a (γ₀ - δ)
    ‖qCLM curvedRegularU 2‖
    (qRange_hadj curvedRegularU) (piCLM_symm curvedRegularU DeltaPrimePi hPiSym) hPsym hγδ
    (qCLM_norm_pos (by norm_num) witL5_dvd_two witL5_wide_two curvedRegularU)
    (hDPa_of_source_chain curvedRegularU DeltaPrimePi P a γ₀ δ h310a hpi hPpos)
    (qRange_surjective (qCLM curvedRegularU 2)) (qRange_le curvedRegularU) B

end Punchlines

/-! ## §7 — axiom audit -/

#print axioms bridge_witness_mem_W
#print axioms bridge_witness_Q_eq
#print axioms bridge_forces_Q_onto_W
#print axioms bridge_hyps_false_of_W_subset_kerQ
#print axioms no_go_must_not_fire_without_hWker
#print axioms no_go_must_not_fire_at_trivial_K
#print axioms qCLM_eq_zero_of_mem_VReg
#print axioms qRange_eq_zero_of_mem_VReg
#print axioms pAbsorb
#print axioms fineCLM_absorb
#print axioms pAbsorb_inner
#print axioms pAbsorb_symm
#print axioms pAbsorb_pos
#print axioms hDP_pAbsorb_of_hDPa
#print axioms bridge_constructed_a_absorbed
#print axioms H310A
#print axioms h310a_holds_on_VReg
#print axioms h310a_at_dirConstField_iff
#print axioms dirConstField_satisfies_h310a_at
#print axioms LinkFixed
#print axioms axisCompatible_of_linkFixed
#print axioms RMap_inv_of_fixed
#print axioms RMap_periodicPathHolonomy_of_linkFixed
#print axioms rZeroA_dirConstField
#print axioms lineCoarseRestrictCov_dirConstField
#print axioms qCLM_dirConstField_ne_zero
#print axioms rotGenVal
#print axioms rotGenVal_mem
#print axioms rotGen
#print axioms rotGenVal_ne_zero
#print axioms rotGen_ne_zero
#print axioms RMap_rotElem_rotGen
#print axioms curvedRegularU_linkFixes_rotGen
#print axioms zeroCoarseBond
#print axioms zeroCoarseBond_dir
#print axioms zeroCoarseBond_block_card_pos
#print axioms qCLM_dirConstField_ne_zero_at_curvedRegularU
#print axioms dirConstField_not_mem_VReg_at_curvedRegularU
#print axioms dirConstField_satisfies_h310a_at_curvedRegularU
#print axioms bridge_at_VReg_hypotheses_unsatisfiable
#print axioms bridge_at_VReg_unsatisfiable_at_realQ
#print axioms bridge_at_VReg_unsatisfiable_at_curvedRegularU
#print axioms norm_qRange_eq
#print axioms hDPa_of_source_chain
#print axioms bridge_source_chain_a_augmented_at_curvedRegularU

/-! ## §8 — DOES THE `a`-TERM REPAIR, OR RELOCATE? THE DECISIVE TEST

`H310A` was reached by observing that the `a`-term SEES the constant null field (§5). The honest
next question — asked of my own repair — is whether `Δ_k` has a null direction that `Q` does NOT
see. It does.

Generalise `dirConstField` from a CONSTANT to any profile depending only on the `d`-coordinate:

  `axisField d c X b := if b.2 = d then (c b.1) • X else 0`.

For `X` link-fixed and `c` invariant under transverse shifts, the covariant curl still vanishes at
every plaquette (the two surviving terms cancel exactly as before), and all four `A′` are ℝ-multiples
of the SAME `X`, so every commutator in `Δ′`'s second term dies. Hence the `Δ_k` form is `0` — for
EVERY such `c`, not just `c ≡ 1`.

`Q`, on the other hand, integrates `c` along the `d`-axis. If `c` ALTERNATES —
`c x + c (x + e_d) = 0` — the two-term line integral cancels POINTWISE, at every block site, so
`Q` is `0` at every coarse bond with no block enumeration at all.

Such a `c` exists at `witL5` (`altC x := (-1)^{(x 0)}`, well defined because the axis has an EVEN
number of sites, `L 0 + 1 = 6`). So

  **`H310A curvedRegularU γ a` is FALSE for every `γ > 0` and every `a`.**

The `a`-term repairs the CONSTANT mode and nothing more. `Δ_k`'s null space contains a
`Q`-invisible direction, and no choice of `a` reaches it. What is left to carry that direction is
`P` — the gauge-fixing term — which is exactly where `bridge_constructed_a_absorbed`'s hypothesis
`hDPa` still has it. So the `curvedRegularU` chain in §6b must be read with `hDPa` as its real
input; `hDPa_of_source_chain` (the route through `h310a`) is a DEAD ROUTE and is marked so below.

This is reported as a FACT about my own construction. The grading is not mine. -/

section AxisFieldRefutation

open AdalyFormal.Balaban.CovariantOperators (curlValueCovariant)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm covPlaqInner hsInner_zero_zero)
open AdalyFormal.Balaban.DeltaPrime (AprimeXY AprimeYZ AprimeZW AprimeWX commutatorMatrixSum
  deltaPrimeFirstTerm deltaPrimeSecondTerm deltaPrimePlaqTerm deltaPrimeQuadForm)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_ell2 transportPath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply)
open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU
  deltaKQuadFormNormalizedCorrected_eq_sub)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)

variable {L : PeriodicLatticeExtent}

/-- **The axis field with a profile.** `c ≡ 1` recovers `H310Satisfiability.dirConstField`. -/
noncomputable def axisField (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) :
    Bond L → SuTwo :=
  fun b => if b.2 = d then (c b.1) • X else 0

/-- Every value is an ℝ-multiple of the SAME `X` — the form used everywhere below, so that no
lemma needs a case split. -/
theorem axisField_eq_smul (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (b : Bond L) :
    axisField d c X b = (if b.2 = d then c b.1 else 0) • X := by
  show (if b.2 = d then (c b.1) • X else 0) = (if b.2 = d then c b.1 else 0) • X
  by_cases h : b.2 = d
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_smul]

theorem axisField_pair (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo)
    (x : PeriodicLatticeSite L) (e : Fin 3) :
    axisField d c X (x, e) = (if e = d then c x else 0) • X :=
  axisField_eq_smul d c X (x, e)

/-- `RMap` of ANY group element fixing `X`, applied to an axis-field value. Stated for a general
element because the transports in `rZeroA` are HOLONOMIES, not single link values. -/
theorem RMap_axisField_of_fixed (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hg : RMap g X = X) (b' : Bond L) :
    RMap g (axisField d c X b') = (if b'.2 = d then c b'.1 else 0) • X := by
  rw [axisField_eq_smul, map_smul, hg]

/-- The link-value case. -/
theorem RMap_axisField
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (b b' : Bond L) :
    RMap (U b) (axisField d c X b') = (if b'.2 = d then c b'.1 else 0) • X :=
  RMap_axisField_of_fixed (U b) d c X (hfix b) b'

/-! ### §8a — the `Δ_k` form vanishes on EVERY transverse-invariant axis field -/

/-- **The covariant curl vanishes at every plaquette.** Same two-term cancellation as
`H310Satisfiability.curl_dirConstField_eq_zero`, now with a profile: the surviving pair is
`c x • X` against `c (x + e_transverse) • X`, equal by transverse invariance. -/
theorem curl_axisField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (hc : ∀ (x : PeriodicLatticeSite L) (ν : Fin 3), ν ≠ d →
      c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x ν) = c x)
    (p : AdalyFormal.Target.ClayStatement.PeriodicLatticePlaquette L) :
    curlValueCovariant U (axisField d c X) p = 0 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  show axisField d c X (p.1, p.2.1.1)
      + RMap (U (p.1, p.2.1.1))
          (axisField d c X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1,
            p.2.1.2))
      - RMap (U (p.1, p.2.1.2))
          (axisField d c X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2,
            p.2.1.1))
      - axisField d c X (p.1, p.2.1.2) = 0
  have hR : ∀ (b : Bond L) (r : ℝ), RMap (U b) (r • X) = r • X := by
    intro b r
    rw [map_smul, hfix b]
  simp only [axisField_pair, hR]
  by_cases hmu : p.2.1.1 = d
  · have hnu : p.2.1.2 ≠ d := fun h => hne (hmu.trans h.symm)
    rw [if_pos hmu, if_neg hnu, if_neg hnu, if_pos hmu, hc p.1 p.2.1.2 hnu]
    module
  · by_cases hnu : p.2.1.2 = d
    · rw [if_neg hmu, if_pos hnu, if_pos hnu, if_neg hmu, hc p.1 p.2.1.1 hmu]
      module
    · rw [if_neg hmu, if_neg hnu, if_neg hnu, if_neg hmu]
      module

/-- **All six commutators die when the four `A′` are ℝ-multiples of one `X`.** -/
theorem commutatorMatrixSum_eq_zero_of_all_smul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : AdalyFormal.Target.ClayStatement.PeriodicLatticePlaquette L)
    (X : SuTwo) (r1 r2 r3 r4 : ℝ)
    (h1 : (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) = r1 • (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = r2 • (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) = r3 • (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) = r4 • (X : Matrix (Fin 2) (Fin 2) ℂ)) :
    commutatorMatrixSum U A p = 0 := by
  have key : ∀ (r s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      (r • M) * (s • M) - (s • M) * (r • M) = 0 := by
    intro r s M
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm r s, sub_self]
  show Complex.I • (((AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ)
        - (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ))
      + ((AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ)
        - (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ))
      + ((AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ)
        - (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ))
      + ((AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ)
        - (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ))
      + ((AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ)
        - (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ))
      + ((AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ)
        - (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) * (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ)))
      = 0
  rw [h1, h2, h3, h4, key r1 r2, key r1 r3, key r1 r4, key r2 r3, key r2 r4, key r3 r4]
  simp

/-- **The commutator sum vanishes on every axis field over a link-fixed `X`.** -/
theorem commutatorMatrixSum_axisField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (p : AdalyFormal.Target.ClayStatement.PeriodicLatticePlaquette L) :
    commutatorMatrixSum U (axisField d c X) p = 0 := by
  refine commutatorMatrixSum_eq_zero_of_all_smul U _ p X
    (-(if p.2.1.1 = d then c (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2)
        else 0))
    (-(if p.2.1.2 = d then c p.1 else 0))
    (if p.2.1.1 = d then c p.1 else 0)
    (if p.2.1.2 = d then c (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1)
        else 0) ?_ ?_ ?_ ?_
  · show ((-(RMap (U (p.1, p.2.1.2))
        (axisField d c X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2,
          p.2.1.1))) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [RMap_axisField U d c X hfix _
      (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2, p.2.1.1)]
    push_cast
    module
  · show ((-(axisField d c X (p.1, p.2.1.2)) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [axisField_pair]
    push_cast
    module
  · show ((axisField d c X (p.1, p.2.1.1) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [axisField_pair]
    push_cast
    rfl
  · show ((RMap (U (p.1, p.2.1.1))
        (axisField d c X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1,
          p.2.1.2)) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [RMap_axisField U d c X hfix _
      (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1, p.2.1.2)]
    push_cast
    rfl

/-- **`⟨A,Δ_k A⟩ = 0` on every transverse-invariant axis field over a link-fixed `X`.** -/
theorem deltaKQuadFormNormalizedCorrected_axisField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (hc : ∀ (x : PeriodicLatticeSite L) (ν : Fin 3), ν ≠ d →
      c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x ν) = c x) :
    deltaKQuadFormNormalizedCorrected U (axisField d c X) = 0 := by
  have hds : dstarDQuadForm U (axisField d c X) = 0 := by
    unfold dstarDQuadForm covPlaqInner
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [curl_axisField_eq_zero U d c X hfix hc p, hsInner_zero_zero]
  have hdp : deltaPrimeQuadForm U (axisField d c X) = 0 := by
    unfold deltaPrimeQuadForm
    refine Finset.sum_eq_zero (fun p _ => ?_)
    have hfirst : deltaPrimeFirstTerm U (axisField d c X) p = 0 := by
      unfold deltaPrimeFirstTerm
      rw [curl_axisField_eq_zero U d c X hfix hc p]
      simp
    have hsecond : deltaPrimeSecondTerm U (axisField d c X) p = 0 := by
      unfold deltaPrimeSecondTerm
      rw [commutatorMatrixSum_axisField_eq_zero U d c X hfix p]
      simp
    unfold deltaPrimePlaqTerm
    rw [hfirst, hsecond, add_zero]
  rw [deltaKQuadFormNormalizedCorrected_eq_sub, hds, hdp]
  norm_num

/-! ### §8b — and `Q` does NOT see it, when `c` alternates -/

/-- **`rZeroA` vanishes POINTWISE at `ell = 2`** when `c` alternates along the `d`-axis: the two
transported summands are `c x • X` and `c (x + e_d) • X`, and they cancel. No block enumeration. -/
theorem rZeroA_axisField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (halt : ∀ x : PeriodicLatticeSite L,
      c x + c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x d) = 0)
    (cMinus x : PeriodicLatticeSite L) (μ : Fin 3) :
    rZeroA U cMinus x (axisField d c X) μ 2 = 0 := by
  rw [rZeroA_ell2,
    RMap_axisField_of_fixed _ d c X
      (RMap_periodicPathHolonomy_of_linkFixed U X hfix (transportPath cMinus x μ 0) cMinus) (x, μ),
    RMap_axisField_of_fixed _ d c X
      (RMap_periodicPathHolonomy_of_linkFixed U X hfix (transportPath cMinus x μ 1) cMinus)
      (AdalyFormal.Target.ClayStatement.periodicLatticeShift x μ, μ)]
  by_cases hmu : μ = d
  · subst hmu
    rw [if_pos rfl, if_pos rfl, ← add_smul, halt x, zero_smul]
  · rw [if_neg hmu, if_neg hmu, zero_smul, add_zero]

/-- **`Q` annihilates the alternating axis field, at every coarse bond.** -/
theorem lineCoarseRestrictCov_axisField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (halt : ∀ x : PeriodicLatticeSite L,
      c x + c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x d) = 0)
    (b : CoarseBond L 2) :
    lineCoarseRestrictCov U 2 (axisField d c X) b = 0 := by
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 2,
      rZeroA U b.1.1 x (axisField d c X) b.2 2 = 0
  rw [Finset.sum_eq_zero
      (fun x _ => rZeroA_axisField_eq_zero U d c X hfix halt b.1.1 x b.2), smul_zero]

theorem qCLM_axisField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (halt : ∀ x : PeriodicLatticeSite L,
      c x + c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x d) = 0) :
    qCLM U 2 (WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L) = 0 := by
  have hpt : ∀ b : CoarseBond L 2,
      WithLp.ofLp (qCLM U 2 (WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L)) b = 0 := by
    intro b
    rw [qCLM_apply]
    exact lineCoarseRestrictCov_axisField_eq_zero U d c X hfix halt b
  calc qCLM U 2 (WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L)
      = WithLp.toLp 2
        (WithLp.ofLp (qCLM U 2 (WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L))) := rfl
    _ = WithLp.toLp 2 (fun _ : CoarseBond L 2 => (0 : SuTwo)) := by rw [funext hpt]
    _ = 0 := rfl

/-- The axis field is a NONZERO vector as soon as `c` is somewhere nonzero and `X ≠ 0`. -/
theorem toLp_axisField_ne_zero (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo)
    (hX : X ≠ 0) (x₀ : PeriodicLatticeSite L) (hc₀ : c x₀ ≠ 0) :
    (WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L) ≠ 0 := by
  intro hcon
  have h : axisField (L := L) d c X (x₀, d) = (0 : SuTwo) :=
    congrFun (congrArg (fun u : BondFnL2 L => WithLp.ofLp u) hcon) (x₀, d)
  rw [axisField_pair, if_pos rfl] at h
  rcases smul_eq_zero.1 h with h1 | h1
  · exact hc₀ h1
  · exact hX h1

/-! ### §8c — THE REFUTATION OF `H310A` -/

/-- **`H310A U γ a` IS FALSE**, at every background carrying a link-fixed nonzero `X` and a
transverse-invariant ALTERNATING profile, for every `γ > 0` and EVERY `a`. -/
theorem H310A_false_of_alternating_axisField
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X) (hX : X ≠ 0)
    (hc : ∀ (x : PeriodicLatticeSite L) (ν : Fin 3), ν ≠ d →
      c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x ν) = c x)
    (halt : ∀ x : PeriodicLatticeSite L,
      c x + c (AdalyFormal.Target.ClayStatement.periodicLatticeShift x d) = 0)
    (x₀ : PeriodicLatticeSite L) (hc₀ : c x₀ ≠ 0)
    (γ a : ℝ) (hγ : 0 < γ) :
    ¬ H310A U γ a := by
  intro h310a
  have hv := h310a (axisField d c X)
  rw [deltaKQuadFormNormalizedCorrected_axisField_eq_zero U d c X hfix hc,
    qCLM_axisField_eq_zero U d c X hfix halt, norm_zero] at hv
  have hne := toLp_axisField_ne_zero (L := L) d c X hX x₀ hc₀
  have hpos : 0 < ‖(WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L)‖ := by
    rcases (norm_nonneg (WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L)).lt_or_eq with h | h
    · exact h
    · exact absurd (norm_eq_zero.1 h.symm) hne
  have hsq : 0 < ‖(WithLp.toLp 2 (axisField (L := L) d c X) : BondFnL2 L)‖ ^ 2 := pow_pos hpos 2
  nlinarith [mul_pos hγ hsq, hv]

/-! ### §8d — the concrete alternating profile at `witL5`, and the verdict at `curvedRegularU`

`witL5 μ = 5`, so each axis carries `6` sites. `6` is EVEN, which is exactly what makes an
alternating profile well defined on the periodic axis. -/

/-- `altC x = (-1)^{(x 0)}`. -/
def altC (x : PeriodicLatticeSite witL5) : ℝ := if (x 0).val % 2 = 0 then 1 else -1

/-- Transverse invariance: `altC` reads only coordinate `0`, and a shift in direction `ν ≠ 0`
does not change it (`Function.update_of_ne`). -/
theorem altC_transverse (x : PeriodicLatticeSite witL5) (ν : Fin 3) (hν : ν ≠ (0 : Fin 3)) :
    altC (AdalyFormal.Target.ClayStatement.periodicLatticeShift x ν) = altC x := by
  have hshift : (AdalyFormal.Target.ClayStatement.periodicLatticeShift x ν) 0 = x 0 := by
    show (Function.update x ν (x ν + 1)) 0 = x 0
    exact Function.update_of_ne (fun h => hν h.symm) _ _
  unfold altC
  rw [hshift]

/-- Alternation along the `0`-axis: `6` sites, so the parity genuinely flips at the wraparound. -/
theorem altC_alternates (x : PeriodicLatticeSite witL5) :
    altC x + altC (AdalyFormal.Target.ClayStatement.periodicLatticeShift x (0 : Fin 3)) = 0 := by
  have hshift : (AdalyFormal.Target.ClayStatement.periodicLatticeShift x (0 : Fin 3)) 0
      = x 0 + 1 := by
    show (Function.update x (0 : Fin 3) (x 0 + 1)) 0 = x 0 + 1
    exact Function.update_self _ _ _
  unfold altC
  rw [hshift]
  have h6 : ∀ j : Fin 6,
      (if j.val % 2 = 0 then (1 : ℝ) else -1) + (if ((j + 1 : Fin 6)).val % 2 = 0 then 1 else -1)
        = 0 := by
    intro j
    fin_cases j <;> norm_num [Fin.add_def]
  exact h6 (x 0)

theorem altC_at_zero_ne_zero : altC (fun _ => 0) ≠ 0 := by
  show (if ((fun _ : Fin 3 => (0 : Fin (witL5 0 + 1))) 0).val % 2 = 0 then (1 : ℝ) else -1) ≠ 0
  norm_num

/-- **THE VERDICT ON MY OWN REPAIR.** At `curvedRegularU` — the flagship's background, where §5
proves the CONSTANT null field IS seen by `Q` — the ALTERNATING null field is NOT, and `H310A` is
false for every `γ > 0` and every `a`. The `a`-term does not repair the (3.10) hypothesis. -/
theorem H310A_false_at_curvedRegularU (γ a : ℝ) (hγ : 0 < γ) :
    ¬ H310A curvedRegularU γ a :=
  H310A_false_of_alternating_axisField curvedRegularU (0 : Fin 3) altC rotGen
    curvedRegularU_linkFixes_rotGen rotGen_ne_zero altC_transverse altC_alternates
    (fun _ => 0) altC_at_zero_ne_zero γ a hγ

/-- **AND THE CONTRAST IS REAL, not an artefact of the field family.** On the SAME background, over
the SAME link-fixed `X`, in the SAME direction, `Q` sees the constant profile
(`qCLM_dirConstField_ne_zero_at_curvedRegularU`) and annihilates the alternating one. So `Q`'s
blindness is a property of the PROFILE, and §5's `Q`-visibility result is not vacuous. -/
theorem qCLM_axisField_altC_eq_zero_at_curvedRegularU :
    qCLM curvedRegularU 2
        (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) : BondFnL2 witL5) = 0 :=
  qCLM_axisField_eq_zero curvedRegularU (0 : Fin 3) altC rotGen
    curvedRegularU_linkFixes_rotGen altC_alternates

end AxisFieldRefutation

#print axioms axisField
#print axioms axisField_eq_smul
#print axioms axisField_pair
#print axioms RMap_axisField_of_fixed
#print axioms RMap_axisField
#print axioms curl_axisField_eq_zero
#print axioms commutatorMatrixSum_eq_zero_of_all_smul
#print axioms commutatorMatrixSum_axisField_eq_zero
#print axioms deltaKQuadFormNormalizedCorrected_axisField_eq_zero
#print axioms rZeroA_axisField_eq_zero
#print axioms lineCoarseRestrictCov_axisField_eq_zero
#print axioms qCLM_axisField_eq_zero
#print axioms toLp_axisField_ne_zero
#print axioms H310A_false_of_alternating_axisField
#print axioms altC
#print axioms altC_transverse
#print axioms altC_alternates
#print axioms altC_at_zero_ne_zero
#print axioms H310A_false_at_curvedRegularU
#print axioms qCLM_axisField_altC_eq_zero_at_curvedRegularU

/-! ## §9 — WHAT SURVIVES, AND EXACTLY WHAT IS LEFT TO PROVE

§8 refuted `h310a`. This section (a) states the resulting vacuity of §6b's chain in the tree rather
than in prose, (b) supplies the chain that does NOT route through `h310a`, and (c) proves precisely
what the alternating null field demands of the surviving hypothesis. -/

section Survives

open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.BridgeInverse (qCLM CoarseFnL2 qRange qRangeStar qRange_hadj qRange_le
  qRange_surjective piCLM piCLM_apply piCLM_symm qCLM_norm_pos nontrivial_range_curved
  witL5_dvd_two witL5_wide_two sOp qstar_injective_of_surjective)

/-- **THE `a`-AUGMENTED CHAIN'S OWN BINDERS YIELD `False`.** The `hγδ` and `h310a` binders below are
character-for-character those of `bridge_source_chain_a_augmented_at_curvedRegularU`, and the unused
`hreal` FEEDS the full list to it, forcing type identity. `hpi` at the alternating field forces
`δ ≥ 0`, `hγδ` then forces `γ₀ > 0`, and §8 kills `h310a` at every positive `γ₀`.

Same shape as `H310Satisfiability.flagship_application_is_vacuous`, applied to my own construction
rather than to someone else's. -/
theorem bridge_source_chain_a_augmented_hypotheses_unsatisfiable
    (DeltaPrimePi P : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (a γ₀ δ : ℝ)
    (hPiSym : ∀ u v : BondFnL2 witL5,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 witL5, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγδ : 0 < γ₀ - δ)
    (h310a : H310A curvedRegularU γ₀ a)
    (hpi : ∀ x : BondFnL2 witL5, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 witL5, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (B : (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2))) :
    False := by
  have hreal := bridge_source_chain_a_augmented_at_curvedRegularU DeltaPrimePi P a γ₀ δ
    hPiSym hPsym hγδ h310a hpi hPpos B
  clear hreal
  have hvne := toLp_axisField_ne_zero (L := witL5) (0 : Fin 3) altC rotGen rotGen_ne_zero
    (fun _ => 0) altC_at_zero_ne_zero
  have hvpos : 0 < ‖(WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
      BondFnL2 witL5)‖ := by
    rcases (norm_nonneg (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
      BondFnL2 witL5)).lt_or_eq with h | h
    · exact h
    · exact absurd (norm_eq_zero.1 h.symm) hvne
  have hdelta : 0 ≤ δ := by
    have h := hpi (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
      BondFnL2 witL5)
    have hsq : 0 < ‖(WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
      BondFnL2 witL5)‖ ^ 2 := pow_pos hvpos 2
    nlinarith [abs_nonneg (inner ℝ (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
      BondFnL2 witL5) (DeltaPrimePi (WithLp.toLp 2
        (axisField (L := witL5) (0 : Fin 3) altC rotGen) : BondFnL2 witL5)) : ℝ), h, hsq]
  exact H310A_false_at_curvedRegularU γ₀ a (by linarith) h310a

set_option maxHeartbeats 8000000 in
/-- **THE LIVE CHAIN AT `curvedRegularU`.** Identical construction to
`bridge_source_chain_a_augmented_at_curvedRegularU` — same `Q`, same `Q*`, same constructed `G₁`
and `S`, same fine operator `Δ_π + P + Q*aQ` — but the coercivity input is `hDPa` DIRECTLY, with
`⟨x,Px⟩` intact. No `h310a`, so §8's refutation does not touch it.

The conclusion has no `− a‖B‖²` term: that is the price of absorbing `a • Q*Q` into `P`, and it
makes this bound WEAKER than `BridgeInverse.bridge_source_chain_at_curvedRegularU`'s at the same
`γ, q`. It is also not vacuous, which that one is. -/
theorem bridge_source_chain_hDPa_at_curvedRegularU
    (DeltaPrimePi P : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (a γ : ℝ)
    (hPiSym : ∀ u v : BondFnL2 witL5,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 witL5, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγ : 0 < γ)
    (hDPa : ∀ x : BondFnL2 witL5, γ * ‖x‖ ^ 2
      ≤ (inner ℝ x (piCLM curvedRegularU DeltaPrimePi x) : ℝ) + (inner ℝ x (P x) : ℝ)
        + a * ‖qRange (qCLM curvedRegularU 2) x‖ ^ 2)
    (B : (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2))) :
    (γ / ‖qCLM curvedRegularU 2‖ ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp (piCLM curvedRegularU DeltaPrimePi)
            (pAbsorb P (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a)
            (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) 0 γ
            (qRange_hadj curvedRegularU) hγ le_rfl
            (hDP_pAbsorb_of_hDPa (piCLM curvedRegularU DeltaPrimePi) P
              (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a γ
              (qRange_hadj curvedRegularU) hDPa)
            (qstar_injective_of_surjective _ _ (qRange_hadj curvedRegularU)
              (qRange_surjective (qCLM curvedRegularU 2))) B) : ℝ) :=
  letI := nontrivial_range_curved
  bridge_constructed_a_absorbed (piCLM curvedRegularU DeltaPrimePi) P
    (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a γ
    ‖qCLM curvedRegularU 2‖
    (qRange_hadj curvedRegularU) (piCLM_symm curvedRegularU DeltaPrimePi hPiSym) hPsym hγ
    (qCLM_norm_pos (by norm_num) witL5_dvd_two witL5_wide_two curvedRegularU)
    hDPa (qRange_surjective (qCLM curvedRegularU 2)) (qRange_le curvedRegularU) B

/-- **THE NAMED RESIDUAL, AS A THEOREM RATHER THAN A LABEL.**

At the alternating null field `v` the `Δ_k` term is `0` (§8) and the `a`-term is `0` (§8), so the
surviving hypothesis `hDPa` collapses to a demand on the GAUGE-FIXING TERM ALONE:

  `(γ − δ)‖v‖² ≤ ⟨v, P v⟩`.

So supplying `hDPa` at `curvedRegularU` REQUIRES `P` to be coercive, with constant `γ − δ`, on the
closed alternating mode. Nothing in the tree supplies that, and nothing here does either — but it
is now a precise statement about a named object rather than "the coercivity is open". -/
theorem alternating_field_forces_P_coercive
    (DeltaPrimePi P : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (a γ δ : ℝ)
    (hpi : ∀ x : BondFnL2 witL5, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hDPa : ∀ x : BondFnL2 witL5, γ * ‖x‖ ^ 2
      ≤ (inner ℝ x (piCLM curvedRegularU DeltaPrimePi x) : ℝ) + (inner ℝ x (P x) : ℝ)
        + a * ‖qRange (qCLM curvedRegularU 2) x‖ ^ 2) :
    (γ - δ) * ‖(WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
        BondFnL2 witL5)‖ ^ 2
      ≤ (inner ℝ (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) : BondFnL2 witL5)
          (P (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) :
            BondFnL2 witL5)) : ℝ) := by
  set v : BondFnL2 witL5 :=
    (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) : BondFnL2 witL5) with hvdef
  have hQ : qRange (qCLM curvedRegularU 2) v = 0 :=
    Subtype.ext qCLM_axisField_altC_eq_zero_at_curvedRegularU
  have hDk : (inner ℝ v (deltaKCLMNormalized curvedRegularU v) : ℝ) = 0 := by
    rw [hvdef, inner_deltaKCLMNormalized_eq curvedRegularU
      (axisField (L := witL5) (0 : Fin 3) altC rotGen)]
    exact deltaKQuadFormNormalizedCorrected_axisField_eq_zero curvedRegularU (0 : Fin 3) altC
      rotGen curvedRegularU_linkFixes_rotGen altC_transverse
  have hmain := hDPa v
  rw [piCLM_apply, inner_sub_right, hDk, hQ, norm_zero] at hmain
  have h2 : (inner ℝ v (DeltaPrimePi v) : ℝ) ≥ -(δ * ‖v‖ ^ 2) :=
    neg_le_of_abs_le (hpi v)
  nlinarith [hmain, h2]

end Survives

#print axioms bridge_source_chain_a_augmented_hypotheses_unsatisfiable
#print axioms bridge_source_chain_hDPa_at_curvedRegularU
#print axioms alternating_field_forces_P_coercive

/-! ## §10 — THE LIVE CHAIN IS NOT VACUOUS: AN EXPLICIT INHABITANT

Everything above says what CANNOT be done. This section discharges §9's `hDPa` outright, so
`bridge_source_chain_hDPa_at_curvedRegularU` acquires an UNCONDITIONAL instance — the property the
flagship chain provably lacks.

**Read the scope honestly.** The `P` used here is `(γ + ‖Δ_k‖) • id`, a large multiple of the
identity. It is a legitimate value of the bridge's `P` slot (symmetric, positive semidefinite) but
it is NOT CMP99b's gauge-fixing term, and this section therefore establishes NOTHING about the
source's (3.156). What it does establish, and what nothing else in the chain does, is that the
bridge machinery at `curvedRegularU` has a real inhabitant: `hG1`, `hTS`, `hadj`, `hQ`,
surjectivity, symmetry AND the coercivity input are simultaneously satisfied, and the coarse bound
`(γ/q²)‖B‖² ≤ ⟨B,SB⟩` genuinely holds for it, at every `γ > 0`. -/

section Inhabitant

open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized)
open AdalyFormal.Balaban.BridgeInverse (qCLM CoarseFnL2 qRange qRangeStar qRange_hadj qRange_le
  qRange_surjective piCLM piCLM_apply piCLM_symm qCLM_norm_pos nontrivial_range_curved
  witL5_dvd_two witL5_wide_two sOp qstar_injective_of_surjective)

/-- The witness `P`: `(γ + ‖Δ_k‖) • id`. Big enough to dominate `Δ_k`'s most negative direction,
which is all that is asked of it here. -/
noncomputable def bigP (γ : ℝ) : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5 :=
  (γ + ‖deltaKCLMNormalized curvedRegularU‖) • ContinuousLinearMap.id ℝ (BondFnL2 witL5)

theorem bigP_inner (γ : ℝ) (x : BondFnL2 witL5) :
    (inner ℝ x (bigP γ x) : ℝ) = (γ + ‖deltaKCLMNormalized curvedRegularU‖) * ‖x‖ ^ 2 := by
  show (inner ℝ x ((γ + ‖deltaKCLMNormalized curvedRegularU‖) • x) : ℝ) = _
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem bigP_symm (γ : ℝ) (u v : BondFnL2 witL5) :
    (inner ℝ u (bigP γ v) : ℝ) = (inner ℝ (bigP γ u) v : ℝ) := by
  show (inner ℝ u ((γ + ‖deltaKCLMNormalized curvedRegularU‖) • v) : ℝ)
      = (inner ℝ ((γ + ‖deltaKCLMNormalized curvedRegularU‖) • u) v : ℝ)
  rw [real_inner_smul_right, real_inner_smul_left]

theorem bigP_pos (γ : ℝ) (hγ : 0 < γ) (x : BondFnL2 witL5) :
    (0 : ℝ) ≤ (inner ℝ x (bigP γ x) : ℝ) := by
  rw [bigP_inner]
  have h1 : (0 : ℝ) ≤ ‖deltaKCLMNormalized curvedRegularU‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  positivity

/-- `Δ_k` is bounded below by `−‖Δ_k‖‖x‖²` — the only property of `Δ_k` this section uses. -/
theorem deltaK_inner_ge (x : BondFnL2 witL5) :
    -(‖deltaKCLMNormalized curvedRegularU‖ * ‖x‖ ^ 2)
      ≤ (inner ℝ x (deltaKCLMNormalized curvedRegularU x) : ℝ) := by
  have h1 : |(inner ℝ x (deltaKCLMNormalized curvedRegularU x) : ℝ)|
      ≤ ‖x‖ * ‖deltaKCLMNormalized curvedRegularU x‖ := abs_real_inner_le_norm _ _
  have h2 : ‖deltaKCLMNormalized curvedRegularU x‖
      ≤ ‖deltaKCLMNormalized curvedRegularU‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h3 : ‖x‖ * ‖deltaKCLMNormalized curvedRegularU x‖
      ≤ ‖x‖ * (‖deltaKCLMNormalized curvedRegularU‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
  have h4 := neg_abs_le (inner ℝ x (deltaKCLMNormalized curvedRegularU x) : ℝ)
  nlinarith [h1, h3, h4]

/-- **`hDPa` DISCHARGED**, at `Δ′_π = 0`, `P = bigP γ`, `a = 0`, for every `γ > 0`. -/
theorem hDPa_at_bigP (γ : ℝ) (x : BondFnL2 witL5) :
    γ * ‖x‖ ^ 2
      ≤ (inner ℝ x (piCLM curvedRegularU (0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) x) : ℝ)
        + (inner ℝ x (bigP γ x) : ℝ)
        + 0 * ‖qRange (qCLM curvedRegularU 2) x‖ ^ 2 := by
  rw [piCLM_apply, bigP_inner]
  show γ * ‖x‖ ^ 2
      ≤ (inner ℝ x (deltaKCLMNormalized curvedRegularU x
            - (0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) x) : ℝ)
        + (γ + ‖deltaKCLMNormalized curvedRegularU‖) * ‖x‖ ^ 2
        + 0 * ‖qRange (qCLM curvedRegularU 2) x‖ ^ 2
  rw [show ((0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) x) = 0 from rfl, sub_zero]
  nlinarith [deltaK_inner_ge x]

theorem piCLM_zero_symm (u v : BondFnL2 witL5) :
    (inner ℝ u ((0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) v) : ℝ)
      = (inner ℝ ((0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) u) v : ℝ) := by
  show (inner ℝ u (0 : BondFnL2 witL5) : ℝ) = (inner ℝ (0 : BondFnL2 witL5) v : ℝ)
  rw [inner_zero_right, inner_zero_left]

set_option maxHeartbeats 8000000 in
/-- **AN UNCONDITIONAL COARSE BOUND AT `curvedRegularU`.** No hypothesis but `0 < γ`. The bridge
machinery of `BridgeInverse` — constructed `G₁`, constructed `S`, the faithful covariant `Q` and
its adjoint — is run end to end, and the (3.156)-shaped bound `(γ/q²)‖B‖² ≤ ⟨B,SB⟩` comes out.

**This is a consistency result, not a physics result.** `Δ′_π = 0` and `P` is a large multiple of
the identity, neither of which is CMP99b's object. Its whole content is that the chain in §9 is
INHABITED — which `BridgeInverse.bridge_source_chain_at_curvedRegularU` provably is not
(`H310Satisfiability.flagship_application_is_vacuous`) and which the `h310a` route in §6b provably
is not either (`bridge_source_chain_a_augmented_hypotheses_unsatisfiable`, §9). -/
theorem bridge_bound_unconditional_at_curvedRegularU (γ : ℝ) (hγ : 0 < γ)
    (B : (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2))) :
    (γ / ‖qCLM curvedRegularU 2‖ ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp (piCLM curvedRegularU (0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5))
            (pAbsorb (bigP γ) (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) 0)
            (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) 0 γ
            (qRange_hadj curvedRegularU) hγ le_rfl
            (hDP_pAbsorb_of_hDPa (piCLM curvedRegularU (0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5))
              (bigP γ) (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) 0 γ
              (qRange_hadj curvedRegularU) (hDPa_at_bigP γ))
            (qstar_injective_of_surjective _ _ (qRange_hadj curvedRegularU)
              (qRange_surjective (qCLM curvedRegularU 2))) B) : ℝ) :=
  bridge_source_chain_hDPa_at_curvedRegularU
    (0 : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (bigP γ) 0 γ
    piCLM_zero_symm (bigP_symm γ) hγ (hDPa_at_bigP γ) B

end Inhabitant

#print axioms bigP
#print axioms bigP_inner
#print axioms bigP_symm
#print axioms bigP_pos
#print axioms deltaK_inner_ge
#print axioms hDPa_at_bigP
#print axioms piCLM_zero_symm
#print axioms bridge_bound_unconditional_at_curvedRegularU

end AdalyFormal.Balaban.BridgeRestricted
