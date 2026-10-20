/-
Copyright (c) 2026 Project Adaly. All rights reserved.
-/
import AdalyFormal.Balaban.TowerOneStep

/-!
# `range(G ∘ Q*)` — WHAT IT IS, AND WHAT IT DOES NOT EXCLUDE

`TowerOneStep` §4b′ restates the one-step tower law against the strictly weaker hypothesis
`Rung.next_coercive_gf_on_range` — the gauge-fixed bound demanded only at the points
`RecursiveBridge.bridge_bare` actually evaluates, i.e. at `G(Q*C)`. §10e of that module records,
correctly, that its whole-space refutation (`ExtentUniformCoercivity.un_augmented_coercivity_false`)
does not touch the on-range form, because **nothing in the tree places the refuting witness in
`range(G ∘ Q*)`.**

This module answers that question. The answer is negative for the on-range form as stated, and the
negative answer is a theorem, not a failure to build:

* **§2 — the range is exactly an `M`-preimage.** `G = M⁻¹` is a two-sided inverse
  (`TowerOneStep.Rung.M_G_right` / `G_M_left`), so
  `x ∈ range(G ∘ Q*) ↔ M x ∈ range(Q*)` (`mem_range_iff`). Everything else follows from this one
  line. The conjectured mechanism — "range elements are `M`-harmonic extensions of coarse data" —
  is **proved** here (`inner_M_eq_zero_of_mem_range`, `inner_M_add_of_mem_range`,
  `mem_range_is_M_minimiser`) rather than assumed.
* **§3 — the range cannot exclude an EXTREMAL vector.** If `Δ x = 0` and `P x = 0` then
  `M x = Q*(a • Q x)` identically, so `x = G(Q*(a • Q x))` **is** in the range
  (`extremal_mem_range`). Hence any vector that refutes the whole-space gauge-fixed bound *in the
  extremal way* refutes the on-range bound too, at the same `γ`
  (`onRangeGF_false_of_extremal`). The `a • Q x` here is the coarse datum whose harmonic extension
  the witness is.
* **§4 — where the source's OWN restriction actually lives.** CMP99b p.428 (adjudicated) says of
  (3.156): *"This form is considered on the subspace
  `{B : B=0 on Λᶜ, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`"* — a subspace of the **coarse** variables `B`,
  i.e. a restriction of the CONCLUSION domain, not of the hypothesis domain. The hypothesis-side
  domain it INDUCES is derived here (`next_coercive_gf_on_subspace`): to conclude only for `B ∈ V`
  one needs the fine bound only at `G(Q*(S B))` for `B ∈ V`, i.e. on `H₁(V)` with `H₁ = G Q* S` of
  (3.129); `range(G ∘ Q*)` is its `V = ⊤` case. The criterion is then exact: an extremal `x`
  satisfies `x = G(Q*(S(Q x)))` (`extremal_eq_hOne_of_coarse`), so **a `V` can rescue the route only
  by EXCLUDING `Q x`** (`subspace_false_of_extremal_of_mem`, `extremal_coarse_datum_ne_zero`).
* **§5 — at the tree's own flat lattice operators the refuting witness IS extremal**, because
  `curlEnergy` and `pAx` both vanish on it (`ExtentUniformCoercivity.curlEnergy_liftedAxisField`,
  `pAx_liftedAxisField`) and both forms are positive semidefinite. So
  `liftedAxisField suTwoWitness ∈ range(G ∘ Q*)` (`witness_mem_range`) and the on-range hypothesis
  is **FALSE** there for every `γ > 0`, at every rung at those operators however built
  (`onRange_false_at_lattice`), taxed form included (`onRangePi_false_at_lattice`).
* **§5a/§5a′ — and this is NOT vacuous.** `TowerOneStep.latticeRungAtDeltaK` derives its
  `hinj`/`hMpos` from the refuted whole-space `hDP`, so a refutation aimed at *that* definition
  would prove nothing. Two rungs at the same operators are therefore BUILT here, by two routes with
  nothing in common: `honestLatticeRung` (any `a > 0`; `hMpos` from
  `FibreAggregate.aggregate_fibre_bound_gamma` on `{QA = 0}` and from `a‖QA‖² > 0` off it) and
  `extentLatticeRung` (`a ≥ C_ext`; `hinj`/`hMpos` taken from
  `ExtentUniformCoercivity.M_injective_whole_space` / `M_posdef_whole_space`, already proved by the
  defect-bound route). `fine_pos_two_routes_agree` records that the two agree where both apply.
* **§5d — and the witness is not special.** `ExtentUniformCoercivity.pAx_suTwoLift` gives
  `P_Ax(suTwoLift 2 F) = 0` for EVERY coarse `F`, and the curl of a lift vanishes for every coarse
  field that depends only on the bond DIRECTION (`flatCurl_siteConstLift` — proved from `μ ≠ ν`
  alone, no case split). So **every nonzero site-constant coarse mode is the coarse datum of an
  extremal vector** (`siteConst_mem_range`, `onRange_false_by_siteConst`), and a replacement `V`
  must exclude all of them, not one vector (`subspace_false_of_siteConst`).
  `axisCoarseMode_eq_siteConst` / `curlEnergy_liftedAxisField_via_family` recover the original
  witness as the direction-`0` member, so the family statement and the tree's existing one agree.

**What is NOT claimed.** Nothing here says Bałaban's (3.156) is wrong. `P` throughout is the tree's
CMP95 (1.10) axial form `pAx`, not (3.128)'s `‖RD*·‖²`
(`ExtentUniformCoercivity`'s own scope note), and `V = ⊤` is this campaign's reading, not the
source's. What is settled is the campaign-internal question §10e left open, plus the exact shape any
replacement restriction must have.
-/

namespace AdalyFormal.Balaban.OnRangeCoercivity

open scoped InnerProductSpace
open AdalyFormal.Balaban.TowerOneStep
open AdalyFormal.Balaban.BridgeInverse (fineCLM fineCLM_apply fineCLM_inner qCLM qstarCLM
  CoarseFnL2 qCLM_hadj qCLM_le qCLM_norm_pos qstar_injective_of_surjective
  qCLM_surjective_trivialU)

/-! ## §1 — ONE HILBERT-SPACE LEMMA

A symmetric positive semidefinite operator annihilates every vector on which its quadratic form
vanishes. Proved by the polarisation/discriminant argument, not cited. -/

section Abstract

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {Δ : H →L[ℝ] H}

/-- **PSD + SYMMETRIC + VANISHING DIAGONAL ⟹ IN THE KERNEL.** `⟨x,Nx⟩ = 0 → N x = 0`.
The proof is the discriminant of `t ↦ ⟨x+tu, N(x+tu)⟩ = 2t⟨u,Nx⟩ + t²⟨u,Nu⟩`, evaluated at
`t = −⟨u,Nx⟩/(⟨u,Nu⟩+1)`. -/
theorem apply_eq_zero_of_inner_self_eq_zero (N : H →L[ℝ] H)
    (hsym : ∀ u v : H, (inner ℝ u (N v) : ℝ) = (inner ℝ (N u) v : ℝ))
    (hpos : ∀ y : H, (0 : ℝ) ≤ (inner ℝ y (N y) : ℝ))
    {x : H} (hx : (inner ℝ x (N x) : ℝ) = 0) : N x = 0 := by
  have key : ∀ u : H, (inner ℝ u (N x) : ℝ) = 0 := by
    intro u
    have hxu : (inner ℝ x (N u) : ℝ) = (inner ℝ u (N x) : ℝ) := by
      rw [hsym x u]; exact real_inner_comm _ _
    have hexp : ∀ t : ℝ, (inner ℝ (x + t • u) (N (x + t • u)) : ℝ)
        = 2 * t * (inner ℝ u (N x) : ℝ) + t ^ 2 * (inner ℝ u (N u) : ℝ) := by
      intro t
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [hx, hxu]
      ring
    have hpoly : ∀ t : ℝ,
        0 ≤ 2 * t * (inner ℝ u (N x) : ℝ) + t ^ 2 * (inner ℝ u (N u) : ℝ) := by
      intro t
      have h := hpos (x + t • u)
      rwa [hexp t] at h
    by_contra hne
    have hd : (0 : ℝ) ≤ (inner ℝ u (N u) : ℝ) := hpos u
    have hd1 : (0 : ℝ) < (inner ℝ u (N u) : ℝ) + 1 := by linarith
    have ht : (-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1))
        * ((inner ℝ u (N u) : ℝ) + 1) = -(inner ℝ u (N x) : ℝ) := by
      field_simp
    have h1 := hpoly (-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1))
    have key2 : 0 ≤ (2 * (-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1))
          * (inner ℝ u (N x) : ℝ)
        + (-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1)) ^ 2 * (inner ℝ u (N u) : ℝ))
        * ((inner ℝ u (N u) : ℝ) + 1) ^ 2 := mul_nonneg h1 (by positivity)
    have expand : (2 * (-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1))
          * (inner ℝ u (N x) : ℝ)
        + (-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1)) ^ 2 * (inner ℝ u (N u) : ℝ))
        * ((inner ℝ u (N u) : ℝ) + 1) ^ 2
        = 2 * ((-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1))
              * ((inner ℝ u (N u) : ℝ) + 1)) * (inner ℝ u (N x) : ℝ)
            * ((inner ℝ u (N u) : ℝ) + 1)
          + ((-(inner ℝ u (N x) : ℝ) / ((inner ℝ u (N u) : ℝ) + 1))
              * ((inner ℝ u (N u) : ℝ) + 1)) ^ 2 * (inner ℝ u (N u) : ℝ) := by
      ring
    rw [expand, ht] at key2
    have hc2 : 0 < (inner ℝ u (N x) : ℝ) ^ 2 := by
      rcases lt_trichotomy (inner ℝ u (N x) : ℝ) 0 with h | h | h
      · nlinarith
      · exact absurd h hne
      · nlinarith
    nlinarith [mul_nonneg hc2.le hd]
  have h := key (N x)
  exact inner_self_eq_zero.mp h

/-! ## §2 — `range(G ∘ Q*)` IS AN `M`-PREIMAGE, AND ITS ELEMENTS ARE `M`-MINIMISERS -/

/-- Membership in the on-range domain, named once so every statement below reads the same shape. -/
def InRange (r : Rung H K Δ) (x : H) : Prop := ∃ C : K, r.G (r.Qstar C) = x

/-- **THE RANGE, CHARACTERISED EXACTLY.** `x ∈ range(G ∘ Q*) ↔ M x ∈ range(Q*)`. This is the whole
content of the range restriction: `G` is a two-sided inverse of `M`, so composing with it merely
transports `range(Q*)` through `M⁻¹`. -/
theorem mem_range_iff (r : Rung H K Δ) (x : H) :
    InRange r x ↔ ∃ C : K, r.M x = r.Qstar C := by
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C, r.M_G_right _⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, by rw [← hC, r.G_M_left]⟩

/-- **RANGE ELEMENTS ARE `M`-ORTHOGONAL TO `ker Q`.** The "harmonic extension of coarse data"
mechanism, as a theorem: `⟨M x, z⟩ = 0` for every `z` with `Q z = 0`. -/
theorem inner_M_eq_zero_of_mem_range (r : Rung H K Δ) {x : H} (hx : InRange r x)
    {z : H} (hz : r.Q z = 0) : (inner ℝ (r.M x) z : ℝ) = 0 := by
  obtain ⟨C, hC⟩ := (mem_range_iff r x).1 hx
  rw [hC, r.hadj z C, hz, inner_zero_right]

/-- The Pythagoras identity that follows: on the `Q`-fibre through a range element the `M`-form
splits with no cross term. -/
theorem inner_M_add_of_mem_range (r : Rung H K Δ) {x : H} (hx : InRange r x)
    {z : H} (hz : r.Q z = 0) :
    (inner ℝ (x + z) (r.M (x + z)) : ℝ)
      = (inner ℝ x (r.M x) : ℝ) + (inner ℝ z (r.M z) : ℝ) := by
  have h1 : (inner ℝ (r.M x) z : ℝ) = 0 := inner_M_eq_zero_of_mem_range r hx hz
  have h2 : (inner ℝ x (r.M z) : ℝ) = (inner ℝ (r.M x) z : ℝ) := r.M_sym x z
  have h3 : (inner ℝ z (r.M x) : ℝ) = (inner ℝ (r.M x) z : ℝ) := real_inner_comm _ _
  simp only [map_add, inner_add_left, inner_add_right]
  rw [h2, h3, h1]
  ring

/-- `M` is positive semidefinite on a rung (its `hMpos` gives strict positivity off `0`). -/
theorem M_nonneg (r : Rung H K Δ) (x : H) : (0 : ℝ) ≤ (inner ℝ x (r.M x) : ℝ) := by
  by_cases h : x = 0
  · subst h; simp
  · exact (r.hMpos x h).le

/-- **`range(G ∘ Q*)` IS THE SET OF `M`-MINIMISERS IN THEIR OWN `Q`-FIBRE.** This is the precise
form of "range elements are minimisers/harmonic extensions of coarse data" — the mechanism the
on-range restriction was conjectured to exploit. It is true. §3 shows it is not enough. -/
theorem mem_range_is_M_minimiser (r : Rung H K Δ) {x : H} (hx : InRange r x)
    {y : H} (hy : r.Q y = r.Q x) :
    (inner ℝ x (r.M x) : ℝ) ≤ (inner ℝ y (r.M y) : ℝ) := by
  have hz : r.Q (y - x) = 0 := by rw [map_sub, hy, sub_self]
  have hsplit := inner_M_add_of_mem_range r hx hz
  rw [show x + (y - x) = y by abel] at hsplit
  have := M_nonneg r (y - x)
  linarith

/-! ## §3 — THE RANGE CANNOT EXCLUDE AN EXTREMAL VECTOR

An **extremal** vector is one on which BOTH `Δ` and `P` vanish. On such a vector
`M x = Δ x + P x + a·Q*Q x` collapses to `Q*(a • Q x)`, which is in `range(Q*)` by inspection — so
by §2 the vector is in `range(G ∘ Q*)`. No restriction to the range can remove it. -/

/-- **THE DECISIVE STRUCTURAL LEMMA.** If `Δ x = 0` and `P x = 0` then `x` is literally the range
element over the coarse datum `a • Q x`. -/
theorem extremal_mem_range (r : Rung H K Δ) {x : H} (hΔx : Δ x = 0) (hPx : r.P x = 0) :
    r.G (r.Qstar (r.a • r.Q x)) = x := by
  have hM : r.M x = r.Qstar (r.a • r.Q x) := by
    show fineCLM Δ r.P r.Q r.Qstar r.a x = _
    rw [fineCLM_apply, hΔx, hPx, zero_add, zero_add, map_smul]
  rw [← hM, r.G_M_left]

/-- The same, from the two quadratic forms rather than the two operator values: a `Δ` that is
positive semidefinite and a `P` that always is (a rung field) turn vanishing diagonals into
vanishing values by §1. -/
theorem extremal_mem_range_of_forms (r : Rung H K Δ)
    (hDpos : ∀ y : H, (0 : ℝ) ≤ (inner ℝ y (Δ y) : ℝ)) {x : H}
    (hΔ : (inner ℝ x (Δ x) : ℝ) = 0) (hP : (inner ℝ x (r.P x) : ℝ) = 0) :
    r.G (r.Qstar (r.a • r.Q x)) = x :=
  extremal_mem_range r
    (apply_eq_zero_of_inner_self_eq_zero Δ r.hDsym hDpos hΔ)
    (apply_eq_zero_of_inner_self_eq_zero r.P r.hPsym r.hPpos hP)

/-- **THE ON-RANGE HYPOTHESIS, NAMED.** Exactly the `hDPrange` slot of
`TowerOneStep.Rung.next_coercive_gf_on_range` (with `D := Δ`) and of
`nextPi_coercive_gf_on_range` (with `D` the uncorrected operator). -/
def OnRangeGF (r : Rung H K Δ) (D : H →L[ℝ] H) (γ : ℝ) : Prop :=
  ∀ C : K, γ * ‖r.G (r.Qstar C)‖ ^ 2
    ≤ (inner ℝ (r.G (r.Qstar C)) (D (r.G (r.Qstar C))) : ℝ)
      + (inner ℝ (r.G (r.Qstar C)) (r.P (r.G (r.Qstar C))) : ℝ)

/-- The on-range hypothesis really is what the repaired tower law consumes: this is
`next_coercive_gf_on_range` restated through `OnRangeGF`, so nothing below can be accused of
refuting a shape the tower does not use. -/
theorem next_coercive_gf_of_onRangeGF (r : Rung H K Δ) {γ : ℝ} (hγ : 0 < γ)
    (h : OnRangeGF r Δ γ) : GammaRecursion.CoerciveOn (⇑r.next) (γ / r.q ^ 2) :=
  r.next_coercive_gf_on_range hγ h

/-- **THE REFUTATION.** A nonzero extremal vector kills the on-range hypothesis at every `γ > 0`,
exactly as it kills the whole-space one. The instantiating coarse datum is `a • Q x`. -/
theorem onRangeGF_false_of_extremal (r : Rung H K Δ) (D : H →L[ℝ] H) {x : H} (hx : x ≠ 0)
    (hmem : r.G (r.Qstar (r.a • r.Q x)) = x)
    (hDx : (inner ℝ x (D x) : ℝ) = 0) (hPx : (inner ℝ x (r.P x) : ℝ) = 0)
    {γ : ℝ} (hγ : 0 < γ) : ¬ OnRangeGF r D γ := by
  intro hcon
  have h := hcon (r.a • r.Q x)
  rw [hmem, hDx, hPx] at h
  have hn : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  nlinarith

/-- **AT `a = 0` NO NONZERO EXTREMAL VECTOR EXISTS** — a degenerate-point control. The refutation
therefore genuinely needs the `Q*aQ` augmentation to be present; it is not an artefact of a
degenerate weight. -/
theorem no_extremal_of_a_eq_zero (r : Rung H K Δ) (ha : r.a = 0) {x : H}
    (hΔx : Δ x = 0) (hPx : r.P x = 0) : x = 0 := by
  have hM : r.M x = 0 := by
    show fineCLM Δ r.P r.Q r.Qstar r.a x = 0
    rw [fineCLM_apply, hΔx, hPx, zero_add, zero_add, ha, zero_smul]
  have h0 : r.M 0 = 0 := map_zero _
  exact r.hinj (by rw [hM, h0] : r.M x = r.M 0)

/-- **MUST-NOT-FIRE.** At `γ ≤ 0` the on-range hypothesis HOLDS whenever `Δ` is positive
semidefinite, so §3's refutation is not a statement that the inequality is malformed — it is a
statement about positive constants only. -/
theorem onRangeGF_of_gamma_nonpos (r : Rung H K Δ) (D : H →L[ℝ] H)
    (hDpos : ∀ y : H, (0 : ℝ) ≤ (inner ℝ y (D y) : ℝ)) {γ : ℝ} (hγ : γ ≤ 0) :
    OnRangeGF r D γ := by
  intro C
  have h1 := hDpos (r.G (r.Qstar C))
  have h2 := r.hPpos (r.G (r.Qstar C))
  nlinarith [sq_nonneg ‖r.G (r.Qstar C)‖]

/-! ## §4 — WHERE THE SOURCE'S OWN RESTRICTION LIVES

CMP99b p.428 restricts the **coarse** variable `B`, i.e. the CONCLUSION domain. The induced
hypothesis-side domain is not `range(G ∘ Q*)` but `H₁(V) = G(Q*(S(V)))`, with `H₁ = G₁Q*(QG₁Q*)⁻¹`
of (3.129). That law is proved here, and then the exact exclusion criterion is derived. -/

/-- **THE ONE-STEP LAW ON A COARSE SUBSPACE.** Conclusion only for `B ∈ V`; hypothesis only at
`G(Q*(S B))` for `B ∈ V`. This is the source-shaped restriction, and it is strictly weaker on both
sides than `next_coercive_gf_on_range`. -/
theorem next_coercive_gf_on_subspace (r : Rung H K Δ) {γ : ℝ} (hγ : 0 < γ) (V : K → Prop)
    (hV : ∀ B : K, V B →
      γ * ‖r.G (r.Qstar (r.S B))‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar (r.S B))) (Δ (r.G (r.Qstar (r.S B)))) : ℝ)
          + (inner ℝ (r.G (r.Qstar (r.S B))) (r.P (r.G (r.Qstar (r.S B)))) : ℝ))
    {B : K} (hB : V B) :
    γ / r.q ^ 2 * ‖B‖ ^ 2 ≤ (inner ℝ B (r.next B) : ℝ) := by
  -- `S B` is the only coarse datum the primitive touches for this `B`; feed the law at it.
  have hpt : γ * ‖r.G (r.Qstar (r.S B))‖ ^ 2
      + r.a * ‖r.Q (r.G (r.Qstar (r.S B)))‖ ^ 2
      ≤ (inner ℝ (r.G (r.Qstar (r.S B))) (r.M (r.G (r.Qstar (r.S B)))) : ℝ) := by
    have hinner := fineCLM_inner Δ r.P r.Q r.Qstar r.a r.hadj (r.G (r.Qstar (r.S B)))
    have h := hV B hB
    show _ ≤ (inner ℝ (r.G (r.Qstar (r.S B)))
      (fineCLM Δ r.P r.Q r.Qstar r.a (r.G (r.Qstar (r.S B)))) : ℝ)
    rw [hinner]
    linarith
  -- from here the argument is `bridge_bare`'s, run at the single point `C := S B`.
  set u : H := r.G (r.Qstar (r.S B)) with hu
  have hTB : r.T (r.S B) = B := r.T_S B
  have hQu : r.Q u = B := by rw [hu]; exact hTB
  have hMu : r.M u = r.Qstar (r.S B) := r.M_G_right _
  have hval : (inner ℝ B (r.S B) : ℝ) = (inner ℝ u (r.M u) : ℝ) := by
    have h1 : (inner ℝ u (r.M u) : ℝ) = (inner ℝ (r.Qstar (r.S B)) u : ℝ) := by
      rw [hMu]
      first
        | exact real_inner_comm _ _
        | exact (real_inner_comm _ _).symm
    rw [h1, r.hadj u (r.S B), hQu]
    first
      | exact real_inner_comm _ _
      | exact (real_inner_comm _ _).symm
  have hQnorm : ‖r.Q u‖ ≤ r.q * ‖u‖ := r.hQ u
  have hBu : ‖B‖ ≤ r.q * ‖u‖ := by rw [← hQu]; exact hQnorm
  have hq0 : (0 : ℝ) < r.q := r.hq
  have hunn : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
  have hBsq : ‖B‖ ^ 2 ≤ r.q ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg B]
  have haQ : r.a * ‖r.Q u‖ ^ 2 = r.a * ‖B‖ ^ 2 := by rw [hQu]
  have hstep : γ * ‖u‖ ^ 2 + r.a * ‖B‖ ^ 2 ≤ (inner ℝ B (r.S B) : ℝ) := by
    rw [hval]; rw [← haQ]; exact hpt
  rw [r.inner_next]
  have hgq : γ / r.q ^ 2 * ‖B‖ ^ 2 ≤ γ * ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **AN EXTREMAL VECTOR IS THE `H₁`-IMAGE OF ITS OWN COARSE DATUM.** `x = G(Q*(S(Q x)))`, i.e.
`x = H₁(Q x)` in (3.129)'s notation. So the subspace-restricted hypothesis is evaluated at `x` as
soon as `V` contains `Q x`. -/
theorem extremal_eq_hOne_of_coarse (r : Rung H K Δ) {x : H}
    (hmem : r.G (r.Qstar (r.a • r.Q x)) = x) :
    r.G (r.Qstar (r.S (r.Q x))) = x := by
  have hT : r.T (r.a • r.Q x) = r.Q x := by
    show r.Q (r.G (r.Qstar (r.a • r.Q x))) = r.Q x
    rw [hmem]
  have hS : r.S (r.Q x) = r.a • r.Q x := by
    refine r.T_injective ?_
    rw [r.T_S, hT]
  rw [hS, hmem]

/-- **THE EXACT EXCLUSION CRITERION.** If the coarse datum `Q x` of a nonzero extremal `x` lies in
`V`, the `V`-restricted hypothesis is false too. Contrapositive: a subspace can only rescue the
route by EXCLUDING `Q x`. -/
theorem subspace_false_of_extremal_of_mem (r : Rung H K Δ) (D : H →L[ℝ] H) (V : K → Prop)
    {x : H} (hx : x ≠ 0) (hmem : r.G (r.Qstar (r.a • r.Q x)) = x)
    (hVx : V (r.Q x))
    (hDx : (inner ℝ x (D x) : ℝ) = 0) (hPx : (inner ℝ x (r.P x) : ℝ) = 0)
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ B : K, V B →
      γ * ‖r.G (r.Qstar (r.S B))‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar (r.S B))) (D (r.G (r.Qstar (r.S B)))) : ℝ)
          + (inner ℝ (r.G (r.Qstar (r.S B))) (r.P (r.G (r.Qstar (r.S B)))) : ℝ)) := by
  intro hcon
  have h := hcon (r.Q x) hVx
  rw [extremal_eq_hOne_of_coarse r hmem, hDx, hPx] at h
  have hn : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  nlinarith

/-- The coarse datum of a nonzero extremal vector is itself nonzero — so "exclude `Q x`" is a real
demand on `V` and not automatically satisfied. -/
theorem extremal_coarse_datum_ne_zero (r : Rung H K Δ) {x : H} (hx : x ≠ 0)
    (hmem : r.G (r.Qstar (r.a • r.Q x)) = x) : r.Q x ≠ 0 := by
  intro h0
  apply hx
  rw [← hmem, h0, smul_zero, map_zero, map_zero]

/-- **A POSITIVE DEFINITE OPERATOR IS INJECTIVE.** Used to supply a rung's `hinj` from its `hMpos`
without routing through a coercivity hypothesis. -/
theorem injective_of_pos_definite (N : H →L[ℝ] H)
    (h : ∀ x : H, x ≠ 0 → (0 : ℝ) < (inner ℝ x (N x) : ℝ)) : Function.Injective N := by
  intro u v huv
  by_contra hne
  have hd : u - v ≠ 0 := sub_ne_zero.2 hne
  have hpos := h (u - v) hd
  rw [map_sub, huv, sub_self, inner_zero_right] at hpos
  exact lt_irrefl 0 hpos

/-- **THE RANGE IS NOT TRIVIAL** — a must-fire control on §2: over a nonzero coarse datum the range
element is nonzero, so `InRange` is not secretly `{0}` and §3's refutation is not about a degenerate
domain. -/
theorem range_elt_ne_zero (r : Rung H K Δ) {C : K} (hC : C ≠ 0) : r.G (r.Qstar C) ≠ 0 := by
  intro h0
  apply hC
  have hM : r.M (r.G (r.Qstar C)) = r.Qstar C := r.M_G_right _
  rw [h0, map_zero] at hM
  exact r.hQstarInj (by rw [← hM, map_zero])

end Abstract

/-! ## §5 — AT THE TREE'S OWN FLAT LATTICE OPERATORS: THE WITNESS IS IN THE RANGE

`Δ := DeltaPrimeOperator.deltaKCLMNormalized (trivialU L)` and `P := AxialCoercivity.pAxCLM
(CoarseLattice L 2) 2` are the operators `TowerOneStep.latticeRungAtDeltaK` is built at.
`ExtentUniformCoercivity.liftedAxisField suTwoWitness` has `curlEnergy = 0` and `pAx = 0`, so it is
EXTREMAL in §3's sense, so it is in `range(G ∘ Q*)`, so the on-range hypothesis is refuted there. -/

section Lattice

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.FullySupplied (suTwoLift)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg
  deltaK_trivialU_eq_curlEnergy)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAx_nonneg pAxCLM pAxCLM_symm pAxCLM_pos
  inner_pAxCLM_eq inner_pAxCLM_eq')
open AdalyFormal.Balaban.FibreAggregate (gammaAgg gammaAgg_pos aggregate_fibre_bound_gamma)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized deltaKCLMNormalized_symm
  inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.IslandBridge (norm_sq_bondFnL2)
open AdalyFormal.Balaban.ExtentUniformCoercivity (coarseEnergy coarseEnergy_nonneg norm_sq_qCLM
  axisCoarseMode liftedAxisField curlEnergy_liftedAxisField pAx_liftedAxisField
  bondEnergy_liftedAxisField_pos q_suTwoLift coarseEnergy_axisCoarseMode_pos)

variable {L : PeriodicLatticeExtent}

/-- `⟨v, Δ_k(1) v⟩` IS the curl energy on the `L²` carrier. -/
theorem inner_deltaK_flat (v : BondFnL2 L) :
    (inner ℝ v (deltaKCLMNormalized (trivialU L) v) : ℝ) = curlEnergy (WithLp.ofLp v) := by
  have h := inner_deltaKCLMNormalized_eq (trivialU L) (WithLp.ofLp v)
  rw [deltaK_trivialU_eq_curlEnergy] at h
  exact h

/-- Hence positive semidefinite — the §1 hypothesis, discharged at the tree's own `Δ`. -/
theorem deltaK_flat_pos (v : BondFnL2 L) :
    (0 : ℝ) ≤ (inner ℝ v (deltaKCLMNormalized (trivialU L) v) : ℝ) := by
  rw [inner_deltaK_flat]
  exact curlEnergy_nonneg _

theorem norm_sq_eq_bondEnergy (v : BondFnL2 L) : ‖v‖ ^ 2 = bondEnergy (WithLp.ofLp v) :=
  norm_sq_bondFnL2 (WithLp.ofLp v)

/-- Coarse energy is strictly positive off a nonzero entry. -/
theorem coarseEnergy_pos {F : CoarseBond L 2 → SuTwo} {c0 : CoarseBond L 2} (h : F c0 ≠ 0) :
    0 < coarseEnergy F := by
  have hle : ‖F c0‖ ^ 2 ≤ coarseEnergy F :=
    Finset.single_le_sum (f := fun c : CoarseBond L 2 => ‖F c‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  have hp : (0 : ℝ) < ‖F c0‖ ^ 2 := pow_pos (norm_pos_iff.2 h) 2
  linarith

/-! ### §5a — A LATTICE RUNG THAT DOES NOT ASSUME THE REFUTED BOUND

`latticeRungAtDeltaK` obtains `hinj` and `hMpos` from the whole-space `hDP`, which §10e of
`TowerOneStep` proves unsatisfiable here — so a refutation aimed at that definition would prove
nothing. `M = Δ + P + Q*aQ` is nevertheless positive definite at these operators, for a reason that
does NOT use `hDP`: on `{QA = 0}` the fibre bound `FibreAggregate.aggregate_fibre_bound_gamma`
supplies `γ_agg·bondEnergy A ≤ ⟨A,Δ_kA⟩ + P_Ax(A)`, and off it `a‖QA‖² > 0`. -/

/-- **`M` IS POSITIVE DEFINITE AT THE FLAT LATTICE OPERATORS, WITH NO WHOLE-SPACE HYPOTHESIS.** -/
theorem lattice_fine_pos {a : ℝ} (ha : 0 < a) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (v : BondFnL2 L) (hv : v ≠ 0) :
    (0 : ℝ) < (inner ℝ v (fineCLM (deltaKCLMNormalized (trivialU L))
      (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2) (qstarCLM (trivialU L) 2) a v) : ℝ) := by
  rw [fineCLM_inner _ _ _ _ _ (qCLM_hadj (trivialU L) 2) v, inner_deltaK_flat, inner_pAxCLM_eq']
  have hbe : (0 : ℝ) < bondEnergy (WithLp.ofLp v) := by
    rw [← norm_sq_eq_bondEnergy]
    exact pow_pos (norm_pos_iff.2 hv) 2
  by_cases hQ : ∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 (WithLp.ofLp v) c = 0
  · have hfib := aggregate_fibre_bound_gamma hdvd (WithLp.ofLp v) hQ
    rw [deltaK_trivialU_eq_curlEnergy] at hfib
    have hg := gammaAgg_pos
    have hQnn : (0 : ℝ) ≤ a * ‖qCLM (trivialU L) 2 v‖ ^ 2 := by positivity
    nlinarith
  · push_neg at hQ
    obtain ⟨c, hc⟩ := hQ
    have hQpos : (0 : ℝ) < ‖qCLM (trivialU L) 2 v‖ ^ 2 := by
      rw [norm_sq_qCLM]
      exact coarseEnergy_pos hc
    have h1 := curlEnergy_nonneg (WithLp.ofLp v)
    have h2 := pAx_nonneg (WithLp.ofLp v) (CoarseLattice L 2) 2
    nlinarith

/-- **THE LATTICE RUNG, BUILT WITHOUT THE REFUTED HYPOTHESIS.** Same `Δ`, `P`, `Q`, `Q*` as
`TowerOneStep.latticeRungAtDeltaK`; `hinj` and `hMpos` from `lattice_fine_pos` instead of from
`hDP`. Its existence is what makes §5b a statement about an inhabited object. -/
noncomputable def honestLatticeRung {a : ℝ} (ha : 0 < a)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1) :
    Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)) where
  Q := qCLM (trivialU L) 2
  Qstar := qstarCLM (trivialU L) 2
  P := pAxCLM (CoarseLattice L 2) 2
  a := a
  q := ‖qCLM (trivialU L) 2‖
  hadj := qCLM_hadj (trivialU L) 2
  ha := ha.le
  hq := qCLM_norm_pos (by norm_num) hdvd hwide _
  hQ := qCLM_le (trivialU L) 2
  hDsym := fun u v => (deltaKCLMNormalized_symm (trivialU L) u v).symm
  hPsym := pAxCLM_symm (CoarseLattice L 2) 2
  hPpos := pAxCLM_pos (CoarseLattice L 2) 2
  hinj := injective_of_pos_definite _ (fun x hx => lattice_fine_pos ha hdvd x hx)
  hMpos := fun x hx => lattice_fine_pos ha hdvd x hx
  hQstarInj := qstar_injective_of_surjective _ _ (qCLM_hadj (trivialU L) 2)
    (qCLM_surjective_trivialU (by norm_num) hdvd)

/-! ### §5a′ — THE SECOND, DE-CORRELATED INHABITANT

`ExtentUniformCoercivity.M_injective_whole_space` / `M_posdef_whole_space` already discharge the two
hard rung fields at these operators, unconditionally for `a ≥ C_ext`, by a route with nothing in
common with §5a's: they run through `defect_bound_at_tree_operators`
(`γ₀‖x‖² ≤ ⟨x,Δx⟩+⟨x,Px⟩+C‖Qx‖²`, `γ₀ = 1/13264896`), not through the `{QA = 0}` fibre bound. Both
routes are exercised, and `fine_pos_two_routes_agree` records that they agree where both apply — a
second computational path on the load-bearing positivity, not a restatement of the first. -/

/-- **THE SAME RUNG FROM THE ALREADY-PROVED EXTENT-UNIFORM ROUTE.** Requires the larger weight
`C_ext ≤ a` (`C_ext > 1024`), which §5a does not; it is included so the refutation does not rest on
this module's own positivity proof alone. -/
noncomputable def extentLatticeRung {a : ℝ}
    (ha : AdalyFormal.Balaban.ExtentUniformCoercivity.cExt ≤ a)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1) :
    Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)) where
  Q := qCLM (trivialU L) 2
  Qstar := qstarCLM (trivialU L) 2
  P := pAxCLM (CoarseLattice L 2) 2
  a := a
  q := ‖qCLM (trivialU L) 2‖
  hadj := qCLM_hadj (trivialU L) 2
  ha := le_trans AdalyFormal.Balaban.ExtentUniformCoercivity.cExt_pos.le ha
  hq := qCLM_norm_pos (by norm_num) hdvd hwide _
  hQ := qCLM_le (trivialU L) 2
  hDsym := fun u v => (deltaKCLMNormalized_symm (trivialU L) u v).symm
  hPsym := pAxCLM_symm (CoarseLattice L 2) 2
  hPpos := pAxCLM_pos (CoarseLattice L 2) 2
  hinj := AdalyFormal.Balaban.ExtentUniformCoercivity.M_injective_whole_space hdvd ha
  hMpos := fun x hx =>
    AdalyFormal.Balaban.ExtentUniformCoercivity.M_posdef_whole_space hdvd ha x hx
  hQstarInj := qstar_injective_of_surjective _ _ (qCLM_hadj (trivialU L) 2)
    (qCLM_surjective_trivialU (by norm_num) hdvd)

/-- **THE TWO POSITIVITY ROUTES AGREE WHERE BOTH APPLY.** `§5a`'s fibre route (any `a > 0`) and
`ExtentUniformCoercivity`'s defect route (`a ≥ C_ext`) both assert strict positivity of `⟨x,Mx⟩` off
`0`; at `a ≥ C_ext` both hypotheses hold and the conclusions coincide. Stated as a conjunction so
the agreement is checked by the kernel rather than asserted in prose. -/
theorem fine_pos_two_routes_agree (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {a : ℝ}
    (ha : AdalyFormal.Balaban.ExtentUniformCoercivity.cExt ≤ a) (x : BondFnL2 L) (hx : x ≠ 0) :
    (0 : ℝ) < (inner ℝ x (fineCLM (deltaKCLMNormalized (trivialU L))
        (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2)
        (qstarCLM (trivialU L) 2) a x) : ℝ)
    ∧ (0 : ℝ) < (inner ℝ x (fineCLM (deltaKCLMNormalized (trivialU L))
        (pAxCLM (CoarseLattice L 2) 2) (qCLM (trivialU L) 2)
        (qstarCLM (trivialU L) 2) a x) : ℝ) :=
  ⟨lattice_fine_pos (lt_of_lt_of_le AdalyFormal.Balaban.ExtentUniformCoercivity.cExt_pos ha)
      hdvd x hx,
    AdalyFormal.Balaban.ExtentUniformCoercivity.M_posdef_whole_space hdvd ha x hx⟩

/-! ### §5b — THE WITNESS, AND THE REFUTATION OF THE ON-RANGE HYPOTHESIS -/

/-- `ExtentUniformCoercivity`'s refutation witness, on the `L²` carrier. -/
noncomputable def witnessVec (L : PeriodicLatticeExtent) : BondFnL2 L :=
  WithLp.toLp 2 (liftedAxisField (L := L) suTwoWitness)

theorem inner_deltaK_witness :
    (inner ℝ (witnessVec L) (deltaKCLMNormalized (trivialU L) (witnessVec L)) : ℝ) = 0 := by
  have h := inner_deltaKCLMNormalized_eq (trivialU L) (liftedAxisField (L := L) suTwoWitness)
  rw [deltaK_trivialU_eq_curlEnergy, curlEnergy_liftedAxisField] at h
  exact h

theorem inner_pAx_witness :
    (inner ℝ (witnessVec L) (pAxCLM (CoarseLattice L 2) 2 (witnessVec L)) : ℝ) = 0 := by
  have h := inner_pAxCLM_eq (CoarseLattice L 2) 2 (liftedAxisField (L := L) suTwoWitness)
  rw [pAx_liftedAxisField] at h
  exact h

theorem witnessVec_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) : witnessVec L ≠ 0 := by
  intro h
  have hbe := bondEnergy_liftedAxisField_pos (L := L) hdvd suTwoWitness_ne_zero
  have hn : ‖witnessVec L‖ ^ 2 = bondEnergy (liftedAxisField (L := L) suTwoWitness) :=
    norm_sq_bondFnL2 _
  rw [h, norm_zero] at hn
  norm_num at hn
  linarith

/-- **THE ANSWER TO §10e's OPEN QUESTION — AT EVERY RUNG AT THESE OPERATORS.** No construction is
assumed: for ANY rung whose index operator is the flat `Δ_k` and whose `P` is the tree's `P_Ax`, the
refutation witness lies in `range(G ∘ Q*)`. -/
theorem witness_mem_range (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) :
    r.G (r.Qstar (r.a • r.Q (witnessVec L))) = witnessVec L := by
  have hPx : (inner ℝ (witnessVec L) (r.P (witnessVec L)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_witness
  exact extremal_mem_range_of_forms r deltaK_flat_pos inner_deltaK_witness hPx

/-- **THE ON-RANGE HYPOTHESIS IS FALSE AT THE TREE'S OWN FLAT LATTICE INSTANCE**, for every `γ > 0`,
at every admissible extent, at EVERY rung at these operators however built. This is the exact
statement `TowerOneStep.Rung.next_coercive_gf_on_range` consumes. -/
theorem onRange_false_at_lattice (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) {γ : ℝ} (hγ : 0 < γ) :
    ¬ OnRangeGF r (deltaKCLMNormalized (trivialU L)) γ := by
  have hPx : (inner ℝ (witnessVec L) (r.P (witnessVec L)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_witness
  exact onRangeGF_false_of_extremal r _ (witnessVec_ne_zero hdvd)
    (witness_mem_range hdvd r hP) inner_deltaK_witness hPx hγ

/-- **AND THE OBJECT IS NOT VACUOUS.** The same refutation, at the rung BUILT in §5a — whose
`hinj`/`hMpos` never touch the refuted whole-space bound. So `onRange_false_at_lattice` is not a
statement about an empty type. -/
theorem onRange_false_at_honestLatticeRung {a : ℝ} (ha : 0 < a)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1)
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ OnRangeGF (honestLatticeRung ha hdvd hwide) (deltaKCLMNormalized (trivialU L)) γ :=
  onRange_false_at_lattice hdvd (honestLatticeRung ha hdvd hwide) rfl hγ

/-- **THE TAXED FORM DIES WITH IT.** For a CORRECTED rung at `Δ_π = Δ_k − Δ′_π`, the `hDPrange`
slot of `nextPi_coercive_gf_on_range` is refuted as soon as the caller's `Δ′_π` annihilates the
witness — in particular at `Δ′_π = 0`, the flat case the tower was built for. Paying the (3.120)
tax does not move this. -/
theorem onRangePi_false_at_lattice (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L)
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (piOp (deltaKCLMNormalized (trivialU L)) Dpi))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) (hDpi : Dpi (witnessVec L) = 0)
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ OnRangeGF r (deltaKCLMNormalized (trivialU L)) γ := by
  have hPx : (inner ℝ (witnessVec L) (r.P (witnessVec L)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_witness
  have hpiOp : piOp (deltaKCLMNormalized (trivialU L)) Dpi (witnessVec L) = 0 := by
    rw [piOp_apply, hDpi, sub_zero]
    exact apply_eq_zero_of_inner_self_eq_zero _
      (fun u v => (deltaKCLMNormalized_symm (trivialU L) u v).symm) deltaK_flat_pos
      inner_deltaK_witness
  have hPzero : r.P (witnessVec L) = 0 := by
    rw [hP]
    exact apply_eq_zero_of_inner_self_eq_zero _ (pAxCLM_symm _ _) (pAxCLM_pos _ _) inner_pAx_witness
  exact onRangeGF_false_of_extremal r _ (witnessVec_ne_zero hdvd)
    (extremal_mem_range r hpiOp hPzero) inner_deltaK_witness hPx hγ

/-- The refutation at the SECOND inhabitant, built from `ExtentUniformCoercivity`'s own already-proved
`hinj`/`hMpos`. So the wall does not depend on §5a's construction either. -/
theorem onRange_false_at_extentLatticeRung {a : ℝ}
    (ha : AdalyFormal.Balaban.ExtentUniformCoercivity.cExt ≤ a)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1)
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ OnRangeGF (extentLatticeRung ha hdvd hwide) (deltaKCLMNormalized (trivialU L)) γ :=
  onRange_false_at_lattice hdvd (extentLatticeRung ha hdvd hwide) rfl hγ

/-! ### §5c — THE COARSE DATUM THE WITNESS SITS OVER

`x = H₁(Q x)` (§4), so any replacement subspace `V` must EXCLUDE `Q x`. Here that coarse datum is
identified explicitly: it is `ExtentUniformCoercivity.axisCoarseMode suTwoWitness`. -/

/-- **`Q` OF THE WITNESS, COMPUTED.** The averaging of the lifted axis field is the axis coarse
mode itself. -/
theorem q_witnessVec (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    qCLM (trivialU L) 2 (witnessVec L)
      = WithLp.toLp 2 (axisCoarseMode (L := L) suTwoWitness) := by
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond L 2 → SuTwo)).injective ?_
  funext c
  show lineCoarseRestrictCov (trivialU L) 2 (liftedAxisField (L := L) suTwoWitness) c = _
  exact q_suTwoLift hdvd (axisCoarseMode suTwoWitness) c

/-- The coarse datum is nonzero, so "exclude it" is a real constraint on any replacement `V`. -/
theorem q_witnessVec_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) : r.Q (witnessVec L) ≠ 0 :=
  extremal_coarse_datum_ne_zero r (witnessVec_ne_zero hdvd) (witness_mem_range hdvd r hP)

/-- **THE SUBSPACE-RESTRICTED HYPOTHESIS DIES TOO, FOR ANY `V` CONTAINING THE WITNESS' COARSE
DATUM** — and in particular for `V = ⊤`, this campaign's reading. A `V` that survives must exclude
`Q(liftedAxisField suTwoWitness)`. -/
theorem subspace_false_at_lattice (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) (V : CoarseFnL2 L 2 → Prop)
    (hVx : V (r.Q (witnessVec L))) {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ B : CoarseFnL2 L 2, V B →
      γ * ‖r.G (r.Qstar (r.S B))‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar (r.S B)))
            (deltaKCLMNormalized (trivialU L) (r.G (r.Qstar (r.S B)))) : ℝ)
          + (inner ℝ (r.G (r.Qstar (r.S B))) (r.P (r.G (r.Qstar (r.S B)))) : ℝ)) := by
  have hPx : (inner ℝ (witnessVec L) (r.P (witnessVec L)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_witness
  exact subspace_false_of_extremal_of_mem r _ V (witnessVec_ne_zero hdvd)
    (witness_mem_range hdvd r hP) hVx inner_deltaK_witness hPx hγ

/-- The `V = ⊤` corollary, spelled out: the campaign's own reading of the source restriction gives
nothing. -/
theorem subspace_top_false_at_lattice (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ B : CoarseFnL2 L 2, True →
      γ * ‖r.G (r.Qstar (r.S B))‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar (r.S B)))
            (deltaKCLMNormalized (trivialU L) (r.G (r.Qstar (r.S B)))) : ℝ)
          + (inner ℝ (r.G (r.Qstar (r.S B))) (r.P (r.G (r.Qstar (r.S B)))) : ℝ)) :=
  subspace_false_at_lattice hdvd r hP (fun _ => True) trivial hγ


/-! ### §5d — THE WITNESS IS NOT SPECIAL: A WHOLE FAMILY OF EXTREMAL VECTORS

`ExtentUniformCoercivity.pAx_suTwoLift` already gives `P_Ax(suTwoLift 2 F) = 0` for **every** coarse
`F`, so extremality of a lift is decided entirely by its curl. The curl of a lift vanishes whenever
the coarse field depends only on the BOND DIRECTION and not on the coarse site — because the two
transported terms of the plaquette are evaluated at coordinates the shift does not move
(`shift_coord_ne`), so all four terms cancel in pairs. `axisCoarseMode w` is the direction-`0`
member of that family (`axisCoarseMode_eq_siteConst`).

Consequence: **every nonzero site-constant coarse mode is the coarse datum of an extremal vector**,
so a subspace `V` that rescues the route must exclude all of them, not merely the one witness. -/

/-- A coarse field depending only on the bond DIRECTION. -/
noncomputable def siteConstCoarse (g : Fin 3 → SuTwo) : CoarseBond L 2 → SuTwo := fun c => g c.2

/-- The lift of a site-constant coarse field, evaluated. -/
theorem suTwoLift_siteConstCoarse (g : Fin 3 → SuTwo) (b : Bond L) :
    suTwoLift 2 (siteConstCoarse (L := L) g) b
      = if (b.1 b.2).val % 2 = 1 then ((2 : ℕ) : ℝ) • g b.2 else 0 := by
  unfold suTwoLift siteConstCoarse
  by_cases h : (b.1 b.2).val % 2 = 2 - 1
  · rw [if_pos h]
  · rw [if_neg h]

/-- A shift in direction `ν` does not move any other coordinate. -/
theorem shift_coord_ne (z : PeriodicLatticeSite L) {ν ρ : Fin 3} (h : ρ ≠ ν) :
    (AdalyFormal.Target.ClayStatement.periodicLatticeShift z ν) ρ = z ρ :=
  Function.update_of_ne h _ _

/-- **THE CURL OF EVERY SITE-CONSTANT LIFT VANISHES.** Uses only `μ ≠ ν` on the plaquette's two
directions — no case split on which pair it is. -/
theorem flatCurl_siteConstLift (g : Fin 3 → SuTwo)
    (p : AdalyFormal.Target.ClayStatement.PeriodicLatticePlaquette L) :
    AdalyFormal.Balaban.CovU1Reduction.flatCurlValue
      (suTwoLift 2 (siteConstCoarse (L := L) g)) p = 0 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  unfold AdalyFormal.Balaban.CovU1Reduction.flatCurlValue
  rw [suTwoLift_siteConstCoarse, suTwoLift_siteConstCoarse, suTwoLift_siteConstCoarse,
    suTwoLift_siteConstCoarse]
  dsimp only
  simp only [shift_coord_ne p.1 hne.symm, shift_coord_ne p.1 hne]
  abel

theorem curlEnergy_siteConstLift (g : Fin 3 → SuTwo) :
    curlEnergy (suTwoLift 2 (siteConstCoarse (L := L) g)) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [flatCurl_siteConstLift g p, norm_zero]
  norm_num

/-- **CROSS-CHECK / TWO PATHS.** `axisCoarseMode` is the direction-`0` member of the family, so
`ExtentUniformCoercivity.curlEnergy_liftedAxisField` is recovered from `curlEnergy_siteConstLift`.
Stated as an equality of the two curl-energy facts so the kernel checks the agreement. -/
theorem axisCoarseMode_eq_siteConst (w : SuTwo) :
    axisCoarseMode (L := L) w = siteConstCoarse (fun ρ => if ρ = 0 then w else 0) := by
  funext c
  show (if c.2 = 0 then w else 0) = _
  by_cases h : c.2 = 0
  · rw [if_pos h]; show w = if c.2 = 0 then w else 0; rw [if_pos h]
  · rw [if_neg h]; show (0 : SuTwo) = if c.2 = 0 then w else 0; rw [if_neg h]

theorem curlEnergy_liftedAxisField_via_family (w : SuTwo) :
    curlEnergy (liftedAxisField (L := L) w) = 0 := by
  show curlEnergy (suTwoLift 2 (axisCoarseMode (L := L) w)) = 0
  rw [axisCoarseMode_eq_siteConst w]
  exact curlEnergy_siteConstLift _

/-- The family member, on the `L²` carrier. -/
noncomputable def siteConstVec (L : PeriodicLatticeExtent) (g : Fin 3 → SuTwo) : BondFnL2 L :=
  WithLp.toLp 2 (suTwoLift 2 (siteConstCoarse (L := L) g))

theorem inner_deltaK_siteConst (g : Fin 3 → SuTwo) :
    (inner ℝ (siteConstVec L g)
      (deltaKCLMNormalized (trivialU L) (siteConstVec L g)) : ℝ) = 0 := by
  have h := inner_deltaKCLMNormalized_eq (trivialU L) (suTwoLift 2 (siteConstCoarse (L := L) g))
  rw [deltaK_trivialU_eq_curlEnergy, curlEnergy_siteConstLift] at h
  exact h

theorem inner_pAx_siteConst (g : Fin 3 → SuTwo) :
    (inner ℝ (siteConstVec L g)
      (pAxCLM (CoarseLattice L 2) 2 (siteConstVec L g)) : ℝ) = 0 := by
  have h := inner_pAxCLM_eq (CoarseLattice L 2) 2 (suTwoLift 2 (siteConstCoarse (L := L) g))
  rw [AdalyFormal.Balaban.ExtentUniformCoercivity.pAx_suTwoLift] at h
  exact h

/-- A site with an ODD coordinate in any chosen direction exists on every admissible extent. -/
theorem exists_odd_site_dir (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (ρ : Fin 3) :
    ∃ z : PeriodicLatticeSite L, (z ρ).val = 1 := by
  have h2 : 2 ≤ L ρ + 1 := Nat.le_of_dvd (Nat.succ_pos _) (hdvd ρ)
  exact ⟨Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite L) ρ ⟨1, by omega⟩,
    by rw [Function.update_self]⟩

theorem siteConstVec_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {g : Fin 3 → SuTwo}
    {ρ : Fin 3} (hg : g ρ ≠ 0) : siteConstVec L g ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_odd_site_dir hdvd ρ
  have hval : suTwoLift 2 (siteConstCoarse (L := L) g) (z, ρ) ≠ 0 := by
    rw [suTwoLift_siteConstCoarse, if_pos (by rw [hz])]
    exact smul_ne_zero (by norm_num) hg
  have hbe : 0 < bondEnergy (suTwoLift 2 (siteConstCoarse (L := L) g)) :=
    AdalyFormal.Balaban.FibreAggregate.bondEnergy_pos _ hval
  intro h
  have hn : ‖siteConstVec L g‖ ^ 2 = bondEnergy (suTwoLift 2 (siteConstCoarse (L := L) g)) :=
    norm_sq_bondFnL2 _
  rw [h, norm_zero] at hn
  norm_num at hn
  linarith

/-- **EVERY SITE-CONSTANT MODE IS IN THE RANGE.** Same construction as `witness_mem_range`, over the
whole family. -/
theorem siteConst_mem_range (r : Rung (BondFnL2 L) (CoarseFnL2 L 2)
      (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) (g : Fin 3 → SuTwo) :
    r.G (r.Qstar (r.a • r.Q (siteConstVec L g))) = siteConstVec L g := by
  have hPx : (inner ℝ (siteConstVec L g) (r.P (siteConstVec L g)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_siteConst g
  exact extremal_mem_range_of_forms r deltaK_flat_pos (inner_deltaK_siteConst g) hPx

/-- **THE WALL IS A FAMILY, NOT A POINT.** For EVERY direction `ρ` and every `g` with `g ρ ≠ 0`, the
on-range hypothesis is refuted. Any replacement subspace must exclude all of these coarse data. -/
theorem onRange_false_by_siteConst (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) {g : Fin 3 → SuTwo} {ρ : Fin 3} (hg : g ρ ≠ 0)
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ OnRangeGF r (deltaKCLMNormalized (trivialU L)) γ := by
  have hPx : (inner ℝ (siteConstVec L g) (r.P (siteConstVec L g)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_siteConst g
  exact onRangeGF_false_of_extremal r _ (siteConstVec_ne_zero hdvd hg)
    (siteConst_mem_range r hP g) (inner_deltaK_siteConst g) hPx hγ

/-- **`Q` OF A FAMILY MEMBER IS THE COARSE MODE ITSELF.** So the excluded set a subspace `V` must
avoid is exactly `{siteConstCoarse g : g ≠ 0}` on the coarse carrier. -/
theorem q_siteConstVec (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (g : Fin 3 → SuTwo) :
    qCLM (trivialU L) 2 (siteConstVec L g)
      = WithLp.toLp 2 (siteConstCoarse (L := L) g) := by
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond L 2 → SuTwo)).injective ?_
  funext c
  show lineCoarseRestrictCov (trivialU L) 2 (suTwoLift 2 (siteConstCoarse (L := L) g)) c = _
  exact q_suTwoLift hdvd (siteConstCoarse g) c

/-- **THE SUBSPACE CRITERION, IN ITS FINAL FORM.** A subspace `V` of coarse fields leaves the
route alive only if it excludes EVERY nonzero site-constant coarse mode. -/
theorem subspace_false_of_siteConst (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) (hQ : r.Q = qCLM (trivialU L) 2)
    (V : CoarseFnL2 L 2 → Prop)
    {g : Fin 3 → SuTwo} {ρ : Fin 3} (hg : g ρ ≠ 0)
    (hVg : V (WithLp.toLp 2 (siteConstCoarse (L := L) g))) {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ B : CoarseFnL2 L 2, V B →
      γ * ‖r.G (r.Qstar (r.S B))‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar (r.S B)))
            (deltaKCLMNormalized (trivialU L) (r.G (r.Qstar (r.S B)))) : ℝ)
          + (inner ℝ (r.G (r.Qstar (r.S B))) (r.P (r.G (r.Qstar (r.S B)))) : ℝ)) := by
  have hPx : (inner ℝ (siteConstVec L g) (r.P (siteConstVec L g)) : ℝ) = 0 := by
    rw [hP]; exact inner_pAx_siteConst g
  have hQ : V (r.Q (siteConstVec L g)) := by
    have hQeq : r.Q (siteConstVec L g)
        = WithLp.toLp 2 (siteConstCoarse (L := L) g) := by
      rw [hQ]
      exact q_siteConstVec hdvd g
    rw [hQeq]
    exact hVg
  exact subspace_false_of_extremal_of_mem r _ V (siteConstVec_ne_zero hdvd hg)
    (siteConst_mem_range r hP g) hQ (inner_deltaK_siteConst g) hPx hγ


/-! ### §5e — A SUBSPACE THAT DOES EXCLUDE THE WHOLE FAMILY, AND IS NOT TRIVIAL

§5d says a replacement `V` must exclude every nonzero site-constant coarse mode. That demand is
satisfiable and does not force `V = {0}`: `VzeroAtOrigin` — "vanish at the three coarse bonds based
at the origin block" — excludes the entire family, and still contains a nonzero element. This is
the anti-vacuity check on the criterion itself: an exclusion that could only be met by the zero
subspace would be no criterion at all.

⚠ This is NOT a claim that the on-range bound holds on `H₁(VzeroAtOrigin)`. Nothing here proves any
positive bound; what is proved is that the obstruction of §5d does not by itself force the
degenerate answer. -/

/-- Vanishing at the three coarse bonds based at the origin block. -/
def VzeroAtOrigin (B : CoarseFnL2 L 2) : Prop :=
  ∀ ρ : Fin 3, WithLp.ofLp B
    (⟨AdalyFormal.Balaban.FibreCoercivity.zeroSite L,
      AdalyFormal.Balaban.FibreCoercivity.zeroSite_coarse⟩, ρ) = 0

/-- **IT EXCLUDES THE WHOLE FAMILY.** -/
theorem VzeroAtOrigin_excludes_siteConst {g : Fin 3 → SuTwo} {ρ : Fin 3} (hg : g ρ ≠ 0) :
    ¬ VzeroAtOrigin (WithLp.toLp 2 (siteConstCoarse (L := L) g)) := fun h => hg (h ρ)

/-- The site with `0`-coordinate `2`; a coarse site, distinct from the origin. -/
noncomputable def twoSite (L : PeriodicLatticeExtent) (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1) :
    PeriodicLatticeSite L :=
  Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite L) 0 ⟨2, by have := hwide 0; omega⟩

theorem twoSite_coarse (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1) :
    twoSite L hwide ∈ CoarseLattice L 2 := by
  refine AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.2 fun μ => ?_
  by_cases h : μ = 0
  · subst h
    show ((Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite L) 0
      (⟨2, _⟩ : Fin (L 0 + 1))) 0).val % 2 = 0
    rw [Function.update_self]
    norm_num
  · show ((Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite L) 0
      (⟨2, _⟩ : Fin (L 0 + 1))) μ).val % 2 = 0
    rw [Function.update_of_ne h, AdalyFormal.Balaban.FibreCoercivity.zeroSite_val]

theorem twoSite_ne_zeroSite (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1) :
    twoSite L hwide ≠ AdalyFormal.Balaban.FibreCoercivity.zeroSite L := by
  intro h
  have h0 : (twoSite L hwide 0).val
      = ((AdalyFormal.Balaban.FibreCoercivity.zeroSite L) 0).val := by rw [h]
  rw [show twoSite L hwide 0 = (⟨2, _⟩ : Fin (L 0 + 1)) from Function.update_self _ _ _,
    AdalyFormal.Balaban.FibreCoercivity.zeroSite_val] at h0
  exact absurd h0 (by norm_num)

open scoped Classical in
/-- A coarse field vanishing on the origin block and constant elsewhere. -/
noncomputable def offOriginMode (w : SuTwo) : CoarseBond L 2 → SuTwo :=
  fun c => if (c.1 : PeriodicLatticeSite L) = AdalyFormal.Balaban.FibreCoercivity.zeroSite L
    then 0 else w

open scoped Classical in
theorem offOriginMode_mem (w : SuTwo) :
    VzeroAtOrigin (WithLp.toLp 2 (offOriginMode (L := L) w)) := by
  intro ρ
  show offOriginMode (L := L) w
      (⟨AdalyFormal.Balaban.FibreCoercivity.zeroSite L,
        AdalyFormal.Balaban.FibreCoercivity.zeroSite_coarse⟩, ρ) = 0
  unfold offOriginMode
  rw [if_pos rfl]

open scoped Classical in
/-- **AND IT IS NOT TRIVIAL.** On any extent wide enough to carry two coarse blocks, `VzeroAtOrigin`
contains a nonzero element. So "exclude every site-constant mode" is a nondegenerate demand. -/
theorem VzeroAtOrigin_nontrivial (hwide : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1) {w : SuTwo} (hw : w ≠ 0) :
    VzeroAtOrigin (WithLp.toLp 2 (offOriginMode (L := L) w))
      ∧ (WithLp.toLp 2 (offOriginMode (L := L) w) : CoarseFnL2 L 2) ≠ 0 := by
  refine ⟨offOriginMode_mem w, ?_⟩
  intro h
  have hval : offOriginMode (L := L) w (⟨twoSite L hwide, twoSite_coarse hwide⟩, 0) = w := by
    unfold offOriginMode
    rw [if_neg (twoSite_ne_zeroSite hwide)]
  have hz : offOriginMode (L := L) w (⟨twoSite L hwide, twoSite_coarse hwide⟩, 0) = 0 := by
    have : WithLp.ofLp (WithLp.toLp 2 (offOriginMode (L := L) w) : CoarseFnL2 L 2)
        (⟨twoSite L hwide, twoSite_coarse hwide⟩, 0) = 0 := by rw [h]; rfl
    exact this
  exact hw (by rw [← hval, hz])

end Lattice

section Axioms

#print axioms apply_eq_zero_of_inner_self_eq_zero
#print axioms InRange
#print axioms mem_range_iff
#print axioms inner_M_eq_zero_of_mem_range
#print axioms inner_M_add_of_mem_range
#print axioms M_nonneg
#print axioms mem_range_is_M_minimiser
#print axioms extremal_mem_range
#print axioms extremal_mem_range_of_forms
#print axioms OnRangeGF
#print axioms next_coercive_gf_of_onRangeGF
#print axioms onRangeGF_false_of_extremal
#print axioms no_extremal_of_a_eq_zero
#print axioms onRangeGF_of_gamma_nonpos
#print axioms next_coercive_gf_on_subspace
#print axioms extremal_eq_hOne_of_coarse
#print axioms subspace_false_of_extremal_of_mem
#print axioms extremal_coarse_datum_ne_zero
#print axioms injective_of_pos_definite
#print axioms range_elt_ne_zero
#print axioms inner_deltaK_flat
#print axioms deltaK_flat_pos
#print axioms norm_sq_eq_bondEnergy
#print axioms coarseEnergy_pos
#print axioms lattice_fine_pos
#print axioms honestLatticeRung
#print axioms extentLatticeRung
#print axioms fine_pos_two_routes_agree
#print axioms onRange_false_at_extentLatticeRung
#print axioms witnessVec
#print axioms inner_deltaK_witness
#print axioms inner_pAx_witness
#print axioms witnessVec_ne_zero
#print axioms witness_mem_range
#print axioms onRange_false_at_lattice
#print axioms onRange_false_at_honestLatticeRung
#print axioms onRangePi_false_at_lattice
#print axioms q_witnessVec
#print axioms q_witnessVec_ne_zero
#print axioms subspace_false_at_lattice
#print axioms siteConstCoarse
#print axioms suTwoLift_siteConstCoarse
#print axioms shift_coord_ne
#print axioms flatCurl_siteConstLift
#print axioms curlEnergy_siteConstLift
#print axioms axisCoarseMode_eq_siteConst
#print axioms curlEnergy_liftedAxisField_via_family
#print axioms siteConstVec
#print axioms inner_deltaK_siteConst
#print axioms inner_pAx_siteConst
#print axioms exists_odd_site_dir
#print axioms siteConstVec_ne_zero
#print axioms siteConst_mem_range
#print axioms onRange_false_by_siteConst
#print axioms q_siteConstVec
#print axioms subspace_false_of_siteConst
#print axioms VzeroAtOrigin
#print axioms VzeroAtOrigin_excludes_siteConst
#print axioms twoSite
#print axioms twoSite_coarse
#print axioms twoSite_ne_zeroSite
#print axioms offOriginMode
#print axioms offOriginMode_mem
#print axioms VzeroAtOrigin_nontrivial
#print axioms subspace_top_false_at_lattice

end Axioms

end AdalyFormal.Balaban.OnRangeCoercivity
