/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RecursiveBridge
import AdalyFormal.Balaban.BridgeInverseControls

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `GammaRecursion.lean` — what the BRIDGE'S OWN constant does when the bridge is ITERATED

Lane record: `compute/gamma_recursion/PROGRESS.md`.

**The question.** `RecursiveBridge.bridge_from_piExtended_normalized_threeTen` is the tree's
ingredient ⟹ product theorem: (3.10)-coercivity `γ` on `W`, plus a `δ`-bound on (3.120)'s
indefinite correction, plus `‖Q‖ ≤ q`, yields the (3.156)-form bound with constant `(γ − δ)/q²`.
Iterating one RG step to the next therefore transports the constant by some map. **What map, and
does the iterate have a positive uniform lower bound?**

## §0 — INVENTORY BEFORE BUILDING (§READ-FIRST), reported before any construction

Two instruments, as mandated.

* `compute/duplicate_census/concept_index.py --root formal/AdalyFormal/AdalyFormal --like "…"`:
  **0 declarations** matched the concept key.
* Plain grep (`gammaSeq`, `γ_k`, `def … : ℕ → ℝ`, `/ q ^ 2`, `geometric`) over the tree found
  **three genuine pieces of prior art, all reused here rather than rebuilt** (LAW-19):
  1. `Balaban.ConstantA.aSeqAux` / `aSeq` — CMP99b (3.24)'s `a_{j+1} = a·a_j/(a·L⁻² + a_j)`, with
     `aSeqAux_invariant` (a uniform floor), `aSeqAux_one_one_not_bounded_away_from_zero` (the
     degenerate parameter where the floor dies). **This file follows that file's template
     exactly**: recursion, closed form, uniform-bound question, degenerate-point contrast.
  2. `Balaban.ConstantA.usedAt_const` — CMP99b's `a` of (3.16)/(3.156) is the SAME constant at
     every scale (no `k`-dependence), re-derived there from the source. Used below: the recursion
     needs no `a_k` sequence.
  3. `HoleHunt.Gap2.coercB_no_uniform_constant` — the archetype `γ_k = 1/(k+1) → 0` showing
     `∀k∃γ` ⇏ `∃γ∀k`. Same logical shape as §3 here; the content is different (that one is a
     hand-chosen family, this one is the map the bridge itself induces).
  4. `Balaban.ScaleInduction.not_reversePoincareTowerUniform_eight_two` — the *growing-level*
     analogue, already dead. This file is the *fixed-level, iterated-step* analogue and is
     logically independent of it: neither implies the other.

  **Not found anywhere**: any declaration iterating the bridge, any recursion on a coercivity
  constant, any statement about `(γ − δ)/q²` beyond the single-step conclusion. *(This last clause
  stands. See the correction immediately below for what the FIRST-PASS grep missed.)*

  **CORRECTION, MADE BY THIS LANE AGAINST ITSELF (S75, in place, original retained struck).** The
  §0 grep above was run on the RECURSION vocabulary and was structurally incapable of returning the
  bridge's own INSTANTIATION, which names nothing in that vocabulary. It was found only when §7b
  went looking for a normed coarse carrier. ~~"no `‖qCLM …‖` occurrence outside this file"~~ is
  **FALSE**:

  * `Balaban/BridgeInverseCarrier.lean` builds the coarse `L²` carrier `CoarseFnL2 L ell`, the real
    `Q` as a continuous linear map `qCLM U ell`, its genuine adjoint `qstarCLM`, and proves `hadj`.
  * `Balaban/BridgeInverseControls.lean` §6 proves `qCLM_norm_pos` (`0 < ‖qCLM U ell‖`) and
    `qCLM_le` (the bridge's `hQ` at `q = ‖qCLM U ell‖`), and §7/§9/§10 instantiate the WHOLE bridge
    at that `q` — `bridge_at_lattice_trivialU` and `bridge_source_chain_at_curvedRegularU`, the
    latter at a genuinely curved background with `hG1` and `hTS` **constructed, not assumed**.

  This makes the present file's subject sharper, not weaker: the recursion below does not run at a
  hypothetical `q`, it runs at `‖qCLM U ell‖`, a definite real number the tree already carries.
  What is still absent, and re-grepped after the correction: **no declaration anywhere bounds
  `‖qCLM U ell‖` against `1`** — `qCLM_norm_pos` gives only `> 0`.

## §0a — THE RECURSION, DERIVED, NOT ASSUMED

The dispatch relayed `γ_{k+1} = (γ_k − δ)/q²`. Read off the theorem's actual conclusion:

`bridge_from_piExtended_normalized_threeTen` concludes
`((γ − δ)/q²)‖B‖² ≤ ⟨B, S B⟩ − a‖B‖²`.

The right-hand side is CMP99b (3.156) at `J = 0`: `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ = ⟨B,Δ_k B⟩`
(source trail and the bare, unsubscripted `a` are re-derived in `Balaban/ConstantA.lean` §1, from
CMP99b (3.16) p.393 and (3.156) p.428). So the next level's operator is
`Δ' B = S B − a • B` (`coarse156` below), the RHS is exactly `⟨B, Δ' B⟩`
(`inner_coarse156`), and the constant it inherits is

  **`γ' = (γ − δ)/q²`, with NO `a`** — the `a`-shift is absorbed into `Δ'`, not into the constant.

That is confirmed here as `bridge_step_abstract` and `stepsWith_of_bridge`, both proved
by composing the tree's own `bridge_from_fine_operator` / `piExtended_*` lemmas. The relayed
formula is CORRECT; what it omits is that it is a statement about `Δ'` = the `a`-shifted operator,
which is the only reading under which no `a` appears.

## §0b — WHAT IS PROVED HERE, AND WHAT IS NOT

PROVED (§2–§4): the iterate `gammaSeq` has no uniform positive lower bound whenever `q ≥ 1` and
`δ ≥ 0`, excluding the single degenerate point `q = 1 ∧ δ = 0`; the bound is TIGHT (attained, §4);
and at `q ≥ 1, δ > 0` the iteration does not merely decay — **the bridge's own hypothesis
`0 < γ − δ` fails after finitely many steps**, so the chain cannot be continued at all (§5).

NOT PROVED, and stated plainly: this is a no-go about **what the iterated bridge can certify**, not
about the operators themselves. `CoerciveOn (Δ k) (gammaSeq …)` is a LOWER bound; a chain could
have better constants supplied by some other argument. §4's `chain_attains` closes the obvious
escape by exhibiting an admissible chain whose best constants ARE `gammaSeq γ₀ 0 q k → 0`, so no
better constant is extractable from the step relation alone — but a *different* route remains
logically open, and nothing here speaks against it.

## §0c — `δ` AND `q` ARE FREE (the question underneath)

§6 measures it. `δ` is not free in sign — `hpi` FORCES `δ ≥ 0` on any carrier with a vector of
nonzero norm (`hpi_forces_delta_nonneg`), proved here. `q` is free: `hQ` is an upper bound, so it
is monotone upward in `q` (`hQ_mono`), the useful value is the operator norm, and **no hypothesis
of `bridge_from_piExtended_normalized_threeTen` constrains `q` beyond `0 < q`** — the theorem is
stated for an abstract `Q` on an abstract coarse carrier `K`. Both branches of the dichotomy are
inhabited (§3's kill at `q > 1`, §3's must-not-fire at `q = 1/2`), so the recursion's fate is
decided entirely by a parameter the statement does not pin.
-/

namespace AdalyFormal.Balaban.GammaRecursion

open AdalyFormal.Balaban.RecursiveBridge
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Target.ClayStatement

/-! ## §1 — THE RECURSION AND ITS CLOSED FORMS -/

/-- **The constant the iterated bridge transports.** `gammaSeq γ₀ δ q k` is the coercivity constant
the bridge delivers after `k` steps starting from a level-`0` constant `γ₀`, with a `δ`-bound on
the (3.120) correction and `‖Q‖ ≤ q` at every step. Read directly off
`bridge_from_piExtended_normalized_threeTen`'s conclusion; see `bridge_step_abstract` (§4) for the
derivation, which is a theorem here, not a reading. -/
noncomputable def gammaSeq (γ₀ δ q : ℝ) : ℕ → ℝ
  | 0 => γ₀
  | (k + 1) => (gammaSeq γ₀ δ q k - δ) / q ^ 2

@[simp] theorem gammaSeq_zero (γ₀ δ q : ℝ) : gammaSeq γ₀ δ q 0 = γ₀ := rfl

theorem gammaSeq_succ (γ₀ δ q : ℝ) (k : ℕ) :
    gammaSeq γ₀ δ q (k + 1) = (gammaSeq γ₀ δ q k - δ) / q ^ 2 := rfl

/-- **THE GEOMETRIC UPPER BOUND.** For any non-negative correction bound `δ` and any `q > 0`, the
transported constant is at most `γ₀ / q^{2k}`. No sign hypothesis on `γ₀` is needed: dividing by
`q² > 0` is monotone regardless of sign. -/
theorem gammaSeq_le_geom {γ₀ δ q : ℝ} (hδ : 0 ≤ δ) (hq : 0 < q) (k : ℕ) :
    gammaSeq γ₀ δ q k ≤ γ₀ / q ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    have hstep : gammaSeq γ₀ δ q (n + 1) = (gammaSeq γ₀ δ q n - δ) / q ^ 2 := rfl
    have h1 : (gammaSeq γ₀ δ q n - δ) / q ^ 2 ≤ gammaSeq γ₀ δ q n / q ^ 2 := by
      gcongr
      linarith
    have h2 : gammaSeq γ₀ δ q n / q ^ 2 ≤ (γ₀ / q ^ (2 * n)) / q ^ 2 := by gcongr
    have h3 : (γ₀ / q ^ (2 * n)) / q ^ 2 = γ₀ / q ^ (2 * (n + 1)) := by
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, div_div]
    rw [hstep]
    calc (gammaSeq γ₀ δ q n - δ) / q ^ 2 ≤ gammaSeq γ₀ δ q n / q ^ 2 := h1
      _ ≤ (γ₀ / q ^ (2 * n)) / q ^ 2 := h2
      _ = γ₀ / q ^ (2 * (n + 1)) := h3

/-- **TIGHTNESS: at `δ = 0` the geometric bound is an EQUALITY.** So the decay in
`gammaSeq_le_geom` is not an artefact of a lossy estimate — it is the exact behaviour of the
recursion at the most favourable admissible correction bound. -/
theorem gammaSeq_delta_zero {γ₀ q : ℝ} (k : ℕ) :
    gammaSeq γ₀ 0 q k = γ₀ / q ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hstep : gammaSeq γ₀ 0 q (n + 1) = (gammaSeq γ₀ 0 q n - 0) / q ^ 2 := rfl
    rw [hstep, sub_zero, ih, div_div, ← pow_add, show 2 * n + 2 = 2 * (n + 1) from by ring]

/-- **The `q = 1` closed form**: the correction is subtracted linearly. -/
theorem gammaSeq_q_one {γ₀ δ : ℝ} (k : ℕ) : gammaSeq γ₀ δ 1 k = γ₀ - k * δ := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hstep : gammaSeq γ₀ δ 1 (n + 1) = (gammaSeq γ₀ δ 1 n - δ) / (1 : ℝ) ^ 2 := rfl
    rw [hstep, ih]
    push_cast
    ring

/-- **Every level stays strictly positive when `δ = 0`.** This is what makes the kill sharp: at
`q > 1, δ = 0` the iterated bridge certifies a POSITIVE constant at every single level `k`, and
still has no positive constant serving all `k`. The failure is the uniformity, not the coercivity.
-/
theorem gammaSeq_pos_of_delta_zero {γ₀ q : ℝ} (hγ : 0 < γ₀) (hq : 0 < q) (k : ℕ) :
    0 < gammaSeq γ₀ 0 q k := by
  rw [gammaSeq_delta_zero k]
  positivity

/-! ## §2 — THE UNIFORMITY PREDICATE AND THE NO-GO

`UniformStepGamma δ q` is the strongest form of p.428's `γ₀ > 0` uniform in `k`, restricted to what
the iterated bridge can deliver: it lets the level-`0` constant `γ₀` be chosen as favourably as one
likes, and asks only for SOME positive floor. Refuting it refutes the uniformity for every possible
starting constant. -/

/-- **`[BRIDGE-STEP-UNIFORM]`** — some starting constant `γ₀` whose bridge iterates admit a
positive uniform floor. -/
def UniformStepGamma (δ q : ℝ) : Prop :=
  ∃ γ₀ γmin : ℝ, 0 < γmin ∧ ∀ k : ℕ, γmin ≤ gammaSeq γ₀ δ q k

/-- **THE KILL AT `q > 1`.** With any admissible correction bound `δ ≥ 0` and any `q > 1`, no
starting constant gives the iterated bridge a positive uniform floor: the constants are forced
below every `ε > 0`. Note `δ = 0` is allowed — the kill does NOT need the correction to be
non-trivial. -/
theorem not_uniformStepGamma_of_one_lt {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 1 < q) :
    ¬ UniformStepGamma δ q := by
  rintro ⟨γ₀, γmin, hmin, hall⟩
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have h0 : γmin ≤ γ₀ := by simpa using hall 0
  have hγ0 : (0 : ℝ) < γ₀ := lt_of_lt_of_le hmin h0
  -- `q^2 > 1`, so `(q^2)^n` exceeds `γ₀ / γmin` for some `n`
  have hq2 : (1 : ℝ) < q ^ 2 := by nlinarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (γ₀ / γmin) hq2
  have hbound := le_trans (hall n) (gammaSeq_le_geom hδ hq0 n)
  have hpow : q ^ (2 * n) = (q ^ 2) ^ n := by rw [← pow_mul]
  rw [hpow] at hbound
  have hpos : (0 : ℝ) < (q ^ 2) ^ n := by positivity
  rw [le_div_iff₀ hpos] at hbound
  rw [div_lt_iff₀ hmin] at hn
  nlinarith [hbound, hn, hmin]

/-- **THE KILL AT `q = 1` WITH A NON-TRIVIAL CORRECTION.** Here the constant does not decay
geometrically — it decreases LINEARLY, `γ_k = γ₀ − kδ`, and goes negative. -/
theorem not_uniformStepGamma_one_of_pos_delta {δ : ℝ} (hδ : 0 < δ) :
    ¬ UniformStepGamma δ 1 := by
  rintro ⟨γ₀, γmin, hmin, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((γ₀ - γmin) / δ)
  have h := hall n
  rw [gammaSeq_q_one] at h
  rw [div_lt_iff₀ hδ] at hn
  nlinarith [h, hn]

/-- **THE COMBINED NO-GO.** For every `q ≥ 1` and every admissible `δ ≥ 0`, EXCEPT the single point
`q = 1 ∧ δ = 0`, the iterated bridge has no `k`-uniform positive constant. -/
theorem not_uniformStepGamma_of_one_le {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 1 ≤ q)
    (hnd : ¬ (q = 1 ∧ δ = 0)) : ¬ UniformStepGamma δ q := by
  rcases lt_or_eq_of_le hq with hq1 | hq1
  · exact not_uniformStepGamma_of_one_lt hδ hq1
  · have hq' : q = 1 := hq1.symm
    subst hq'
    have hδpos : 0 < δ := by
      rcases lt_or_eq_of_le hδ with h | h
      · exact h
      · exact absurd ⟨rfl, h.symm⟩ hnd
    exact not_uniformStepGamma_one_of_pos_delta hδpos

/-! ## §3 — MUST-NOT-FIRE CONTROLS AND THE DEGENERATE-POINT INVENTORY

Following `ScaleInduction.lean` §4/§6b's discipline: every parameter point at which the no-go does
NOT fire is compiled, so none of them can be cited as evidence and none of the hypotheses can be
suspected of being decorative. -/

/-- **CONTROL 1 (the excluded point is genuinely excluded).** At `q = 1, δ = 0` the recursion is
the identity, the floor exists, and `not_uniformStepGamma_of_one_le` does not fire. So `hnd` is
load-bearing, not padding. -/
theorem uniformStepGamma_one_zero : UniformStepGamma 0 1 := by
  refine ⟨1, 1, by norm_num, fun k => ?_⟩
  rw [gammaSeq_q_one]
  simp

/-- **CONTROL 2 (a NON-degenerate must-not-fire point).** For `0 < q < 1` the step map is
EXPANDING, and any starting constant at or above the fixed point `δ/(1−q²)` gives a floor. The
theorem's `1 ≤ q` is therefore load-bearing at genuinely non-trivial parameters, not only at a
boundary. -/
theorem uniformStepGamma_of_lt_one {γ₀ δ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hγ : 0 < γ₀) (hfix : δ ≤ γ₀ * (1 - q ^ 2)) : UniformStepGamma δ q := by
  refine ⟨γ₀, γ₀, hγ, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ n ih =>
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    have hq2' : q ^ 2 < 1 := by nlinarith
    have hstep : gammaSeq γ₀ δ q (n + 1) = (gammaSeq γ₀ δ q n - δ) / q ^ 2 := rfl
    rw [hstep, le_div_iff₀ hq2]
    nlinarith [ih, hfix, hq2']

/-- **CONTROL 2, at a concrete non-degenerate point**: `q = 1/2`, `δ = 1`, `γ₀ = 2`. The fixed
point is `δ/(1−q²) = 4/3 < 2`, the iterates GROW (`2, 4, 12, …`), and the floor `2` holds. -/
theorem uniformStepGamma_half_one : UniformStepGamma 1 (1 / 2) :=
  uniformStepGamma_of_lt_one (γ₀ := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The concrete iterates of CONTROL 2, computed: `2, 4, 12`. Exhibited so the control is not just
an existence claim about a floor — the sequence visibly moves the other way. -/
theorem gammaSeq_half_values :
    gammaSeq 2 1 (1 / 2) 1 = 4 ∧ gammaSeq 2 1 (1 / 2) 2 = 12 := by
  constructor
  · show (gammaSeq 2 1 (1 / 2) 0 - 1) / (1 / 2 : ℝ) ^ 2 = 4
    norm_num [gammaSeq]
  · show (gammaSeq 2 1 (1 / 2) 1 - 1) / (1 / 2 : ℝ) ^ 2 = 12
    show ((gammaSeq 2 1 (1 / 2) 0 - 1) / (1 / 2 : ℝ) ^ 2 - 1) / (1 / 2 : ℝ) ^ 2 = 12
    norm_num [gammaSeq]

/-- **DEGENERATE POINT `q = 0`.** The bridge excludes it (`hq : 0 < q`), and it must never be cited
either way: in Lean `x / 0 = 0`, so every iterate after the first is `0` and the floor fails for a
reason that is a division convention, not mathematics. Recorded so the `0 < q` hypothesis is not
mistaken for the source of the kill. -/
theorem gammaSeq_q_zero {γ₀ δ : ℝ} (k : ℕ) : gammaSeq γ₀ δ 0 (k + 1) = 0 := by
  show (gammaSeq γ₀ δ 0 k - δ) / (0 : ℝ) ^ 2 = 0
  simp

/-- **DEGENERATE POINT `γ₀ ≤ 0`.** `UniformStepGamma` demands a POSITIVE floor, and `gammaSeq … 0 =
γ₀`, so a non-positive starting constant refutes it immediately, at every `δ, q`. This is why the
`∃ γ₀` in `UniformStepGamma` is not doing hidden work: the only starting constants that could
possibly satisfy it are the positive ones.

**SELF-CAUGHT DEFECT, recorded rather than silently repaired (S75).** The first draft of this
declaration concluded `∃ γ₀ : ℝ, 0 < γ₀` from `UniformStepGamma δ q`. That conclusion is
**provable outright** (`⟨1, one_pos⟩`) — an existential over data the hypothesis never ties down,
which is exactly the `[[s91-existential-over-free-data]]` class this campaign prosecutes. Restated
so the conclusion is about the WITNESS: -/
theorem uniformStepGamma_witness_pos {δ q γ₀ γmin : ℝ} (hmin : 0 < γmin)
    (hall : ∀ k : ℕ, γmin ≤ gammaSeq γ₀ δ q k) : 0 < γ₀ :=
  lt_of_lt_of_le hmin (by simpa using hall 0)

/-- **A MUST-FIRE CONTROL, CONCRETE.** At `γ₀ = 1, δ = 0, q = 2` the fifth iterate is already
`1/1024 < 1/1000`. The kill is not an asymptotic statement one has to take on trust. -/
theorem gammaSeq_must_fire_concrete : gammaSeq 1 0 2 5 < 1 / 1000 := by
  rw [gammaSeq_delta_zero 5]
  norm_num

/-- **`0 ≤ δ` IS LOAD-BEARING in `gammaSeq_le_geom`** — a mutation that makes the geometric bound
FAIL. At `δ = −1, γ₀ = 1, q = 2` the first iterate is `1/2`, strictly above the bound `γ₀/q² =
1/4`. So the hypothesis is not decoration; and by `hpi_forces_delta_nonneg` (§6) the excluded sign
is not available to the bridge anyway. -/
theorem gammaSeq_le_geom_fails_at_negative_delta :
    ¬ (gammaSeq 1 (-1) 2 1 ≤ 1 / 2 ^ (2 * 1)) := by
  have h : gammaSeq 1 (-1) 2 1 = 1 / 2 := by
    show ((1 : ℝ) - (-1)) / (2 : ℝ) ^ 2 = 1 / 2
    norm_num
  rw [h]
  norm_num

/-! ## §4 — THE DERIVATION FROM THE BRIDGE ITSELF

Everything above is arithmetic about a sequence. This section is the part that makes it a statement
about `RecursiveBridge`: the recursion IS the bridge's constant transform, proved by composing the
bridge's own lemmas. -/

/-- **CMP99b (3.156)'s coarse operator at `J = 0`.** `⟨B, Δ_k B⟩ = ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩`, so
with `S` right-inverting `T = QG₁Q*` the coarse operator is `B ↦ S B − a•B`. The bridge's
conclusion `… ≤ ⟨B,SB⟩ − a‖B‖²` is exactly `… ≤ ⟨B, coarse156 S a B⟩`
(`inner_coarse156`). -/
noncomputable def coarse156 {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (S : K →L[ℝ] K) (a : ℝ) : K → K := fun B => S B - a • B

theorem inner_coarse156 {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (S : K →L[ℝ] K) (a : ℝ) (B : K) :
    (inner ℝ B (coarse156 S a B) : ℝ) = (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 := by
  show (inner ℝ B (S B - a • B) : ℝ) = _
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- **Coercivity of a map on a whole carrier**, the form the recursion transports. -/
def CoerciveOn {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ : H → H) (γ : ℝ) : Prop :=
  ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ)

/-- **THE BRIDGE STEP, ABSTRACT IN `Δ`.** This is
`bridge_from_piExtended_normalized_threeTen` with the concrete `deltaKCLMNormalized U` replaced by
a bound variable `Delta`, so that the OUTPUT of one step can be the INPUT of the next. Proved by
composing the tree's own `bridge_from_fine_operator`, `piExtended_sym` and
`piExtended_coercive_at` — nothing is re-derived.

The conclusion is stated as `CoerciveOn (coarse156 S a) ((γ − δ)/q²)`: **the constant the next
level inherits is `(γ − δ)/q²`, with no `a`.** -/
theorem bridge_step_abstract {L : PeriodicLatticeExtent} {K : Type*}
    [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] [Nontrivial K]
    (Delta DeltaPi P : BondFnL2 L → BondFnL2 L) (W : BondFnL2 L → Prop)
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (T S : K →L[ℝ] K) (a γ δ q : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDeltaSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPi v) : ℝ) = (inner ℝ (DeltaPi u) v : ℝ))
    (hpi : ∀ x : BondFnL2 L, |(inner ℝ x (DeltaPi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hGW : ∀ B : K, W (G (Qstar B)))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 L,
      fineMapOf (piExtendedMap Delta DeltaPi) P Q Qstar a (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγδ : 0 < γ - δ) (hq : 0 < q) (ha : 0 ≤ a)
    (hDeltaCoercW : ∀ x : BondFnL2 L, W x → γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ))
    (hQ : ∀ x : BondFnL2 L, ‖Q x‖ ≤ q * ‖x‖) :
    CoerciveOn (coarse156 S a) ((γ - δ) / q ^ 2) := by
  intro B
  rw [inner_coarse156]
  exact bridge_from_fine_operator (piExtendedMap Delta DeltaPi) P W Q Qstar G T S a (γ - δ) q
    hadj (piExtended_sym Delta DeltaPi hDeltaSym hPiSym) hGW
    (fun x hx => piExtended_coercive_at Delta DeltaPi γ δ x (hDeltaCoercW x hx) (hpi x))
    hPpos hPsym hT hG1 hTS hγδ hq ha hQ B

/-! ### §4a — the step relation, and the iterate

`StepsWith δ q Δ Δ'` abstracts exactly what `bridge_step_abstract` delivers: whatever coercivity
constant `γ` the level-`k` operator has (with `γ − δ > 0`, the bridge's own hypothesis), the
level-`(k+1)` operator inherits `(γ − δ)/q²`. -/

/-- **One admissible bridge step**, as a relation between consecutive operators on one carrier. -/
def StepsWith {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    (δ q : ℝ) (Δ Δ' : H → H) : Prop :=
  ∀ γ : ℝ, 0 < γ - δ → CoerciveOn Δ γ → CoerciveOn Δ' ((γ - δ) / q ^ 2)

/-- `bridge_step_abstract` really does produce a `StepsWith`, on a single fixed carrier
(`K := BondFnL2 L`, the tree's own situation: one torus, no spacing parameter, so every level lives
on the same space). The hypotheses are the bridge's, with the level-`k` operator's coercivity left
as the relation's own antecedent. -/
theorem stepsWith_of_bridge {L : PeriodicLatticeExtent}
    [Nontrivial (BondFnL2 L)]
    (Delta DeltaPi P : BondFnL2 L → BondFnL2 L)
    (Q : BondFnL2 L → BondFnL2 L) (Qstar : BondFnL2 L → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (T S : BondFnL2 L →L[ℝ] BondFnL2 L) (a δ q : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : BondFnL2 L),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDeltaSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPi v) : ℝ) = (inner ℝ (DeltaPi u) v : ℝ))
    (hpi : ∀ x : BondFnL2 L, |(inner ℝ x (DeltaPi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hT : ∀ B : BondFnL2 L, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 L,
      fineMapOf (piExtendedMap Delta DeltaPi) P Q Qstar a (G x) = x)
    (hTS : ∀ B : BondFnL2 L, T (S B) = B)
    (hq : 0 < q) (ha : 0 ≤ a)
    (hQ : ∀ x : BondFnL2 L, ‖Q x‖ ≤ q * ‖x‖) :
    StepsWith δ q Delta (coarse156 S a) := by
  intro γ hγδ hcoerc
  exact bridge_step_abstract Delta DeltaPi P (fun _ => True) Q Qstar G T S a γ δ q
    hadj hDeltaSym hPiSym hpi hPpos hPsym (fun _ => trivial) hT hG1 hTS hγδ hq ha
    (fun x _ => hcoerc x) hQ

/-- **THE ITERATE.** A chain of operators linked by admissible bridge steps carries exactly the
constants `gammaSeq γ₀ δ q k`. The hypothesis `hpos` is the bridge's own `0 < γ − δ` at every
level; §5 shows it is not free. -/
theorem chain_gamma {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    {δ q γ₀ : ℝ} (Δ : ℕ → (H → H))
    (hstep : ∀ k : ℕ, StepsWith δ q (Δ k) (Δ (k + 1)))
    (h0 : CoerciveOn (Δ 0) γ₀)
    (hpos : ∀ k : ℕ, 0 < gammaSeq γ₀ δ q k - δ) :
    ∀ k : ℕ, CoerciveOn (Δ k) (gammaSeq γ₀ δ q k) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ n ih =>
    have := hstep n (gammaSeq γ₀ δ q n) (hpos n) ih
    simpa [gammaSeq_succ] using this

/-- **SHARPNESS: the bound `gammaSeq` is ATTAINED by an admissible chain.** On `H = ℝ` the chain
`Δ_k x = (γ₀/q^{2k})·x` satisfies `StepsWith 0 q` at every step, and its BEST coercivity constant
at level `k` is exactly `gammaSeq γ₀ 0 q k`. So no constant better than `gammaSeq` is extractable
from the step relation alone: the escape "maybe the true constants are larger" is closed at the
level of the relation. -/
theorem chain_attains {γ₀ q : ℝ} (hq : 0 < q) :
    (∀ k : ℕ, StepsWith 0 q (fun x : ℝ => gammaSeq γ₀ 0 q k * x)
      (fun x : ℝ => gammaSeq γ₀ 0 q (k + 1) * x))
    ∧ (∀ (k : ℕ) (γ : ℝ), CoerciveOn (fun x : ℝ => gammaSeq γ₀ 0 q k * x) γ →
        γ ≤ gammaSeq γ₀ 0 q k) := by
  have hinner : ∀ c x : ℝ, (inner ℝ x (c * x) : ℝ) = c * x ^ 2 := by
    intro c x
    rw [Real.inner_apply]
    ring
  have hnorm : ∀ x : ℝ, ‖x‖ ^ 2 = x ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, sq_abs]
  constructor
  · intro k γ _ hc x
    have h1 := hc 1
    rw [hinner, hnorm] at h1
    simp only [one_pow, mul_one] at h1
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    rw [hinner, hnorm]
    have hstep : gammaSeq γ₀ 0 q (k + 1) = (gammaSeq γ₀ 0 q k - 0) / q ^ 2 := rfl
    rw [hstep, sub_zero, sub_zero]
    have hx : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    have : γ / q ^ 2 ≤ gammaSeq γ₀ 0 q k / q ^ 2 := by gcongr
    nlinarith [this, hx]
  · intro k γ hc
    have h1 := hc 1
    rw [hinner, hnorm] at h1
    simpa using h1

/-! ## §5 — THE ITERATION DOES NOT MERELY DECAY: IT STOPS

At `q ≥ 1` and `δ > 0` the chain hypothesis `0 < γ_k − δ` that `chain_gamma` (and the bridge
itself) requires FAILS after finitely many steps. So the iterated-bridge route does not produce a
degrading constant — it produces a chain that cannot be continued. -/

/-- With `q ≥ 1` the iterate loses at least `δ` per step while it is still above `δ`. -/
theorem gammaSeq_step_drop {γ₀ δ q : ℝ} (hq : 1 ≤ q) (k : ℕ)
    (hk : 0 ≤ gammaSeq γ₀ δ q k - δ) :
    gammaSeq γ₀ δ q (k + 1) ≤ gammaSeq γ₀ δ q k - δ := by
  have hq2 : (1 : ℝ) ≤ q ^ 2 := by nlinarith
  have hq2' : (0 : ℝ) < q ^ 2 := by linarith
  show (gammaSeq γ₀ δ q k - δ) / q ^ 2 ≤ gammaSeq γ₀ δ q k - δ
  rw [div_le_iff₀ hq2']
  nlinarith [hk, hq2]

/-- **THE CHAIN BREAKS.** For `q ≥ 1` and `δ > 0` there is a finite `k` at which the bridge's own
hypothesis `0 < γ_k − δ` is false, so `chain_gamma`'s `hpos` cannot hold and the iteration cannot
be carried past step `k`. -/
theorem exists_step_where_bridge_hypothesis_fails {γ₀ δ q : ℝ} (hq : 1 ≤ q) (hδ : 0 < δ) :
    ∃ k : ℕ, ¬ (0 < gammaSeq γ₀ δ q k - δ) := by
  by_contra hcon
  push Not at hcon
  -- every level is above `δ`, so the drop lemma applies at every level
  have hdrop : ∀ k : ℕ, gammaSeq γ₀ δ q (k + 1) ≤ gammaSeq γ₀ δ q k - δ := by
    intro k
    exact gammaSeq_step_drop hq k (le_of_lt (hcon k))
  have hlin : ∀ k : ℕ, gammaSeq γ₀ δ q k ≤ γ₀ - k * δ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have := hdrop n
      push_cast
      nlinarith [this, ih]
  obtain ⟨n, hn⟩ := exists_nat_gt ((γ₀ - δ) / δ)
  have h := hcon n
  have h2 := hlin n
  rw [div_lt_iff₀ hδ] at hn
  nlinarith [h, h2, hn]

/-! ## §6 — ARE `δ` AND `q` PINNED? (the question underneath)

The dispatch's item 4. Measured on the bridge's own signature. -/

/-- **`δ ≥ 0` IS FORCED.** The bridge's `hpi` is a bound on an ABSOLUTE VALUE, so on any carrier
possessing a vector of nonzero norm it forces `δ ≥ 0`. `δ` is therefore not free in sign — but it
is free in magnitude, and the no-go covers every `δ ≥ 0` including `δ = 0`. -/
theorem hpi_forces_delta_nonneg {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : H → H) (δ : ℝ) (hpi : ∀ x : H, |(inner ℝ x (D x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (x₀ : H) (hx₀ : ‖x₀‖ ≠ 0) : 0 ≤ δ := by
  have h := hpi x₀
  have habs : (0 : ℝ) ≤ |(inner ℝ x₀ (D x₀) : ℝ)| := abs_nonneg _
  have hn : (0 : ℝ) < ‖x₀‖ ^ 2 := by
    have := norm_nonneg x₀
    have : (0 : ℝ) < ‖x₀‖ := lt_of_le_of_ne this (Ne.symm hx₀)
    positivity
  nlinarith [h, habs, hn]

/-- The same, on a genuine normed group where `x₀ ≠ 0` suffices. -/
theorem hpi_forces_delta_nonneg' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : H → H) (δ : ℝ) (hpi : ∀ x : H, |(inner ℝ x (D x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (x₀ : H) (hx₀ : x₀ ≠ 0) : 0 ≤ δ :=
  hpi_forces_delta_nonneg D δ hpi x₀ (by simpa using hx₀)

/-- **`q` IS FREE UPWARD**: `hQ` is an upper bound, so it holds at every larger `q`. The bridge's
conclusion is therefore weakest at large `q` and the only value worth supplying is the operator
norm of `Q` — which no hypothesis of the bridge pins. Together with §2 and §3 this says the
recursion's fate is decided by a number the statement does not determine. -/
theorem hQ_mono {H K : Type*} [SeminormedAddCommGroup H] [SeminormedAddCommGroup K]
    (Q : H → K) (q q' : ℝ) (hqq : q ≤ q') (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) :
    ∀ x : H, ‖Q x‖ ≤ q' * ‖x‖ := by
  intro x
  exact le_trans (hQ x) (by nlinarith [norm_nonneg x])

/-- **BOTH BRANCHES ARE INHABITED, at the level of the recursion.** There are admissible `(δ, q)`
for which the uniform floor exists and admissible `(δ, q)` for which it provably does not. So
`UniformStepGamma` is not decided by anything in the bridge's hypotheses: it is decided by `q`. -/
theorem uniformity_is_decided_by_q :
    UniformStepGamma 1 (1 / 2) ∧ ¬ UniformStepGamma 1 2 :=
  ⟨uniformStepGamma_half_one,
   not_uniformStepGamma_of_one_lt (by norm_num) (by norm_num)⟩

/-! ## §7 — WHAT DECIDES `q`: THE NORMALISATION OF THE COARSE-GRAINING

§6 says `q` is unpinned. This section says what pins it in practice, and it is not a subtlety of
the analysis — it is the NORMALISATION CONVENTION of the coarse-graining map, which
`bridge_from_piExtended_normalized_threeTen` leaves entirely abstract (`Q : BondFnL2 L → K` with
`K` an abstract inner-product space).

Modelled on two fine bonds, which is enough to decide the dichotomy:

* a coarse-graining that **SUMS** the fine values over the block forces `1 < q`
  (`summing_forces_one_lt_q`, and the sum map is exhibited, `one_lt_opNorm_projSumTwo`), hence
  the §2 kill fires;
* a coarse-graining that **divides by the block volume** admits `q < 1`
  (`quarterProjSumTwo_bound`), hence §3's must-not-fire applies and the iterate GROWS.

The tree's own coarse-graining, `LineIntegralCovariant.lineCoarseRestrictCov`, carries an explicit
`(1/ell^4)` prefactor, so it sits on the normalised side — but its carriers `BondFnL2 L` and the
`covCoarseBondInner` coarse space are both UNWEIGHTED `ℓ²` (`PiLp 2`, plain `Finset.sum`), with no
measure factor per level. **This file does not compute `‖lineCoarseRestrictCov‖`, and does not
claim to**; what it establishes is that the number deciding p.428's `k`-uniformity, along this
route, is exactly that operator norm, and that both sides of the decision are attainable. -/

/-- The two-bond SUMMING coarse-graining, as a continuous linear map. -/
noncomputable def projSumTwo : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ∑ i : Fin 2, EuclideanSpace.proj i

theorem projSumTwo_apply (x : EuclideanSpace ℝ (Fin 2)) : projSumTwo x = x 0 + x 1 := by
  show (∑ i : Fin 2, EuclideanSpace.proj (𝕜 := ℝ) i) x = _
  simp [Fin.sum_univ_two]

/-- **THE SUMMING CONVENTION FORCES `1 < q`.** Abstract form: if `Q` is additive and takes the
value `1` on each of two orthonormal fine directions, then every `q` for which `‖Q x‖ ≤ q‖x‖`
holds satisfies `1 < q`. No square roots: `‖e₀+e₁‖² = 2` and `Q(e₀+e₁) = 2`, and `q ≤ 1` would
force `‖e₀+e₁‖ ≥ 2`, i.e. `‖e₀+e₁‖² ≥ 4`. -/
theorem summing_forces_one_lt_q {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : H → ℝ) (q : ℝ) (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖)
    (e₀ e₁ : H) (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (horth : (inner ℝ e₀ e₁ : ℝ) = 0)
    (hadd : Q (e₀ + e₁) = Q e₀ + Q e₁) (hQ0 : Q e₀ = 1) (hQ1 : Q e₁ = 1) : 1 < q := by
  have hnorm : ‖e₀ + e₁‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, horth, h0, h1]
    norm_num
  have hval : ‖Q (e₀ + e₁)‖ = 2 := by
    rw [hadd, hQ0, hQ1]
    norm_num
  have hb := hQ (e₀ + e₁)
  rw [hval] at hb
  have hn : (0 : ℝ) ≤ ‖e₀ + e₁‖ := norm_nonneg _
  nlinarith [hb, hn, hnorm]

/-- The summing map on two bonds is an instance: its operator norm exceeds `1`. -/
theorem one_lt_opNorm_projSumTwo : 1 < ‖projSumTwo‖ := by
  refine summing_forces_one_lt_q (fun x => projSumTwo x) ‖projSumTwo‖
    (fun x => projSumTwo.le_opNorm x)
    (EuclideanSpace.single 0 (1 : ℝ)) (EuclideanSpace.single 1 (1 : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [EuclideanSpace.inner_single_left]
    simp
  · exact map_add projSumTwo _ _
  · rw [projSumTwo_apply]
    simp
  · rw [projSumTwo_apply]
    simp

/-- **THE NORMALISED CONVENTION ADMITS `q < 1`.** Dividing the same coarse-graining by the block
"volume" `4` gives an admissible `q = 1/2 < 1`: crudely, `‖projSumTwo‖ ≤ 2` (a sum of two
coordinate projections, each of norm `≤ 1`). -/
theorem opNorm_projSumTwo_le_two : ‖projSumTwo‖ ≤ 2 := by
  have h : ‖projSumTwo‖ ≤ ∑ _i : Fin 2, (1 : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    simpa using PiLp.norm_apply_le x i
  simpa using h

theorem quarterProjSumTwo_bound (x : EuclideanSpace ℝ (Fin 2)) :
    ‖((1 : ℝ) / 4) • projSumTwo x‖ ≤ (1 / 2) * ‖x‖ := by
  have h1 : ‖projSumTwo x‖ ≤ ‖projSumTwo‖ * ‖x‖ := projSumTwo.le_opNorm x
  have h2 := opNorm_projSumTwo_le_two
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  rw [norm_smul]
  simp only [norm_div, Real.norm_ofNat, norm_one]
  nlinarith [h1, h2, hx, norm_nonneg (projSumTwo x)]

/-- **THE CONVENTION DECIDES THE UNIFORMITY, as one statement.** With the SUMMING coarse-graining
the no-go fires at every admissible correction bound; with the block-normalised one the same
recursion has a floor. Nothing in the bridge's hypotheses chooses between them. -/
theorem convention_decides_uniformity {δ : ℝ} (hδ : 0 ≤ δ) :
    ¬ UniformStepGamma δ ‖projSumTwo‖ ∧ UniformStepGamma 1 (1 / 2) :=
  ⟨not_uniformStepGamma_of_one_lt hδ one_lt_opNorm_projSumTwo, uniformStepGamma_half_one⟩

/-! ### §7b — THE NUMBER, IN THE TREE, THAT DECIDES IT

§7's model says the normalisation convention decides `q`. The tree already owns its coarse-graining
as a CONTINUOUS LINEAR MAP between two `L²` carriers —
`BridgeInverse.qCLM U ell : BondFnL2 L →L[ℝ] CoarseFnL2 L ell`, the faithful covariant block
average `LineIntegralCovariant.lineCoarseRestrictCov` (found by the LAW-19 sweep in §0; this file
does not rebuild it). So `‖qCLM U ell‖` EXISTS as a real number in the tree, it supplies the
bridge's `hQ` for free (`qCLM_supplies_hQ`), and it is exactly the number p.428's `k`-uniformity
turns on along this route.

~~**It has not been computed anywhere in the tree** (grepped: no operator-norm bound on `qCLM`, no
`‖qCLM …‖` occurrence outside this file).~~ **STRUCK — the second clause is FALSE**, see the §0
correction: `BridgeInverseControls` uses `‖qCLM …‖` throughout and instantiates the bridge at it.
The clause that SURVIVES re-grepping is the one that matters: **no declaration in the tree bounds
`‖qCLM U ell‖` against `1`**, in either direction; `qCLM_norm_pos` gives only `0 < ‖qCLM U ell‖`.
`lineCoarseRestrictCov` carries a `(1/ell^4)` prefactor
in front of a `blockOf`-sum of line integrals, so it is a normalised average rather than a bare
sum — but both carriers are UNWEIGHTED `PiLp 2` with no per-level measure factor, and this file
neither computes nor guesses the resulting norm. What it does is make the consequence of each
answer a theorem. -/

/-- The tree's own `Q` supplies the bridge's `hQ`, with `q := ‖qCLM U ell‖`.

**LAW-19 DISCLOSURE, self-caught.** This lane first wrote its own proof of this statement. It is
`BridgeInverse.qCLM_le`, already in the tree; the duplicate proof is deleted and the existing
theorem is cited. Kept as a named alias only because the recursion sections read better with the
role in the name. -/
theorem qCLM_supplies_hQ {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (x : BondFnL2 L) :
    ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell x‖
      ≤ ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖ * ‖x‖ :=
  AdalyFormal.Balaban.BridgeInverse.qCLM_le U ell x

/-- **THE DICHOTOMY AT THE TREE'S OWN COARSE-GRAINING.** Both branches, as one theorem, at the real
operator norm. Whichever side `‖qCLM U ell‖` falls on, the answer to "does the iterated bridge give
a `k`-uniform `γ₀ > 0`?" is settled — and no declaration in the tree currently determines which
side that is. -/
theorem tree_Q_decides_uniformity {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (1 < ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖ →
        ¬ UniformStepGamma δ ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖)
    ∧ (∀ γ₀ : ℝ, 0 < γ₀ → 0 < ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖ →
        ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖ < 1 →
        δ ≤ γ₀ * (1 - ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖ ^ 2) →
        UniformStepGamma δ ‖AdalyFormal.Balaban.BridgeInverse.qCLM U ell‖) := by
  refine ⟨fun h => not_uniformStepGamma_of_one_lt hδ h, fun γ₀ hγ hq0 hq1 hfix => ?_⟩
  exact uniformStepGamma_of_lt_one hq0 hq1 hγ hfix

/-- **THE SAME DICHOTOMY AT THE TREE'S ONE FULLY-CONSTRUCTED BRIDGE INSTANCE**, where `0 < q` is
not a hypothesis but a theorem (`BridgeInverse.qCLM_norm_pos`) and `hG1`/`hTS` are constructed
(`BridgeInverse.bridge_source_chain_at_curvedRegularU`, at `curvedRegularU`, a background with
genuine curvature). So the entire question "does the iterated bridge give a `k`-uniform `γ₀ > 0`?"
reduces, at the tree's own instance, to the position of ONE uncomputed real number relative to `1`:
`‖qCLM curvedRegularU 2‖`. -/
theorem curvedRegularU_Q_decides_uniformity {δ : ℝ} (hδ : 0 ≤ δ) :
    (1 < ‖AdalyFormal.Balaban.BridgeInverse.qCLM
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2‖ →
        ¬ UniformStepGamma δ ‖AdalyFormal.Balaban.BridgeInverse.qCLM
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2‖)
    ∧ (∀ γ₀ : ℝ, 0 < γ₀ →
        ‖AdalyFormal.Balaban.BridgeInverse.qCLM
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2‖ < 1 →
        δ ≤ γ₀ * (1 - ‖AdalyFormal.Balaban.BridgeInverse.qCLM
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2‖ ^ 2) →
        UniformStepGamma δ ‖AdalyFormal.Balaban.BridgeInverse.qCLM
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2‖) := by
  have hq0 : 0 < ‖AdalyFormal.Balaban.BridgeInverse.qCLM
      AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2‖ :=
    AdalyFormal.Balaban.BridgeInverse.qCLM_norm_pos (by norm_num)
      AdalyFormal.Balaban.BridgeInverse.witL5_dvd_two
      AdalyFormal.Balaban.BridgeInverse.witL5_wide_two _
  exact ⟨fun h => not_uniformStepGamma_of_one_lt hδ h,
    fun γ₀ hγ hq1 hfix => uniformStepGamma_of_lt_one hq0 hq1 hγ hfix⟩

/-! ## §8 — AXIOM AUDIT -/

#print axioms gammaSeq
#print axioms gammaSeq_zero
#print axioms gammaSeq_succ
#print axioms gammaSeq_le_geom
#print axioms gammaSeq_delta_zero
#print axioms gammaSeq_q_one
#print axioms gammaSeq_pos_of_delta_zero
#print axioms UniformStepGamma
#print axioms not_uniformStepGamma_of_one_lt
#print axioms not_uniformStepGamma_one_of_pos_delta
#print axioms not_uniformStepGamma_of_one_le
#print axioms uniformStepGamma_one_zero
#print axioms uniformStepGamma_of_lt_one
#print axioms uniformStepGamma_half_one
#print axioms gammaSeq_half_values
#print axioms gammaSeq_q_zero
#print axioms uniformStepGamma_witness_pos
#print axioms gammaSeq_must_fire_concrete
#print axioms gammaSeq_le_geom_fails_at_negative_delta
#print axioms coarse156
#print axioms inner_coarse156
#print axioms CoerciveOn
#print axioms bridge_step_abstract
#print axioms StepsWith
#print axioms stepsWith_of_bridge
#print axioms chain_gamma
#print axioms chain_attains
#print axioms gammaSeq_step_drop
#print axioms exists_step_where_bridge_hypothesis_fails
#print axioms hpi_forces_delta_nonneg
#print axioms hpi_forces_delta_nonneg'
#print axioms hQ_mono
#print axioms uniformity_is_decided_by_q
#print axioms projSumTwo
#print axioms projSumTwo_apply
#print axioms summing_forces_one_lt_q
#print axioms one_lt_opNorm_projSumTwo
#print axioms opNorm_projSumTwo_le_two
#print axioms quarterProjSumTwo_bound
#print axioms convention_decides_uniformity
#print axioms qCLM_supplies_hQ
#print axioms tree_Q_decides_uniformity
#print axioms curvedRegularU_Q_decides_uniformity

end AdalyFormal.Balaban.GammaRecursion
