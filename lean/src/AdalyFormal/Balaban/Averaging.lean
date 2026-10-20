/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Blocks
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum.Basic

/-!
# Balaban's averaging operator — eqs. (10)–(15)

Phase-0 REFORM_PROGRAM definitions layer, `PHASE0_DEFS_PLAN.md` item **A1**. Stands alone: no
import of `Target.ClayStatement`.

## Source pin

`corpus/pages/CMP98_p19.md` (`verification_status: adjudicated`), Averaging Operations for
Lattice Gauge Theories, eqs. (10)–(15):

* **(10)** `ϱ'(V) = ∫dU δ(V Ū⁻¹) ϱ(U)` — the RG transformation is an integral operator built from a
  one-step averaging map `U ↦ Ū`. Not encoded directly (requires a Haar-measure integral-operator
  layer that belongs to `WilsonLatticeData`, not this standalone module) — `GaugeCovariant` below
  encodes the property (11) that makes (10) descend to gauge-invariant functions, per the page's
  own argument (12)–(13).
* **(11)** `(Ū^u)(y,y') = u(y) Ū(y,y') u⁻¹(y')`, i.e. `Ū^u = (Ū)^u` — gauge-covariance of the
  averaging map. Transcribed verbatim as `GaugeCovariant` below.
* **(14)** `Ā_c = Σ_{x∈B(c_-)} L^{-(d+1)} (A(Γ_{c_-,x}) + A([x,x(c)]) + A(Γ_{x(c),c_+}))` — the
  LINEAR averaging operation (cited to Balaban's [2], reference [1.8]), valid on Lie-algebra-valued
  configurations near the identity. Weight is `L^{-(d+1)}`.
  **NOT the operator this module encodes** — recorded here only so the two distinct weights are
  never confused (see the WARNING below and `PHASE0_DEFS_PLAN.md`'s own citation of the same
  historical error).
* **(15)** `Ū_c = exp[i Σ_{x∈B(c_-)} L^{-d} (1/i)log(U(Γ_{c,x})U(c)⁻¹)] U(c)` — THE averaging
  operation the paper adopts going forward (p.19: *"we define... an average which satisfies these
  conditions and which has some other advantages"*), reused verbatim by eq. (43)
  (`IteratedAveraging.lean`) for every subsequent RG step. Weight is `L^{-d}`.

**WARNING (load-bearing, repeat of a prior campaign error).** Eq. (14)'s weight is `L^{-(d+1)}`;
eq. (15)'s weight is `L^{-d}`. A previous transcription pass wrote eq. (15)'s weight as
`L^{-(d+1)}` by conflating it with eq. (14)'s; the corpus adjudication (`CMP98_p19.md`
frontmatter, `verification_status: adjudicated`) settled this in favor of `L^{-d}` for eq. (15).
`averageAt` below uses `L^{-d}` and nothing else; `linearAverageAt` (eq. 14, unused downstream)
uses `L^{-(d+1)}` and is kept only as a citation anchor, never composed with `averageAt`.

## Scope

`PHASE0_DEFS_PLAN.md` explicitly separates the STATEMENT SHAPE (any group `G` with abstract
`log`/`exp` primitives into/out of a Lie algebra `𝔤`, matching eq. (15) literally) from the
CONSTRUCTION (a genuine non-abelian Lie-group log/exp, e.g. for `SU(2)`, which is downstream
wiring work). Both eq. (14) and eq. (15) are written here at the general-`G` statement-shape;
the L7 witness instantiates the shape at an ABELIAN `G` where `log`/`exp` are the (honest, exact —
not approximate) group isomorphism `Multiplicative ℚ ≃ ℚ`, since for an abelian one-parameter Lie
group the logarithm IS this isomorphism, not merely a linear approximation to it. This is not a
degenerate shortcut: eq. (15) restricted to abelian `G` is EXACTLY this formula, no approximation
involved. The genuinely open, non-abelian construction (e.g. `G = SU(2)`) is deferred to Phase 2/3
wiring, consistent with `PHASE0_DEFS_PLAN.md`'s A1 classification.
-/

namespace AdalyFormal.Balaban

variable {Site Center G 𝔤 : Type*} [DecidableEq Site]

/-- **Eq. (11), gauge-covariance**: `(Ū^u)(y,y') = u(y) Ū(y,y') u⁻¹(y')`, i.e. `Ū^u = (Ū)^u`.
`Ū : FineConfig → CoarseConfig` is the averaging map; `actFine`/`actCoarse` are the gauge actions
on the fine/coarse link configurations (both instances of `periodicGaugeTransform`'s shape once
wired to a real lattice, kept abstract here so this file stands alone). This is the property that
makes eq. (10)'s transformation descend to gauge-invariant functions, per CMP98 p.19's own argument
(12)-(13). -/
def GaugeCovariant {FineConfig CoarseConfig GaugeFn : Type*}
    (actFine : GaugeFn → FineConfig → FineConfig)
    (actCoarse : GaugeFn → CoarseConfig → CoarseConfig)
    (Ubar : FineConfig → CoarseConfig) : Prop :=
  ∀ (u : GaugeFn) (U : FineConfig), Ubar (actFine u U) = actCoarse u (Ubar U)

/-- **Eq. (14), the linear averaging operation** (cited to Balaban's [2], not this paper's own
adopted definition — see the module WARNING). Weight `L^{-(d+1)}`. `Γcontour c x` stands for the
sum of the three concatenated contour pieces `A(Γ_{c_-,x}) + A([x,x(c)]) + A(Γ_{x(c),c_+})` on
p.19, taken as a single already-summed `𝔤`-value per `x` (the individual contour pieces need the
fine-lattice path-holonomy machinery, deferred exactly as `Averaging.lean`'s GaugeCovariant is).
Kept for citation completeness; not used by `averageAt` or `IteratedAveraging.lean`. -/
noncomputable def linearAverageAt [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (B : Center → Finset Site) (L d : ℕ) (Γcontour : Center → Site → 𝔤) (c : Center) : 𝔤 :=
  ∑ x ∈ B c, ((L : ℚ) ^ (d + 1))⁻¹ • Γcontour c x

/-- **Eq. (15), the adopted averaging operator**: `Ū_c = exp[i Σ_{x∈B(c_-)} L^{-d} (1/i)
log(U(Γ_{c,x}) U(c)⁻¹)] U(c)`. Statement-shape over a general group `G` with an abstract
`log : G → 𝔤` / `exp : 𝔤 → G` pair (the `(1/i)log` / `exp[i·]` pair on the page, with the two `i`s
folded into `log`/`exp` themselves so the formula is written purely in terms of the group `G` and
its Lie algebra `𝔤`), a block map `B`, and a contour-holonomy evaluation `Γ c x` standing for
`U(Γ_{c,x})` (deferred to the fine-lattice path machinery, as in `linearAverageAt`). Weight
`L^{-d}` — see the module WARNING. -/
noncomputable def averageAt [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (log : G → 𝔤) (exp : 𝔤 → G)
    (B : Center → Finset Site) (L d : ℕ)
    (Γ : Center → Site → G) (Uc : Center → G) (c : Center) : G :=
  exp (∑ x ∈ B c, ((L : ℚ) ^ d)⁻¹ • log (Γ c x * (Uc c)⁻¹)) * Uc c

/-! ## L7 witness: the abelian instance `G = Multiplicative ℚ`

For abelian `G`, `log := Multiplicative.toAdd` and `exp := Multiplicative.ofAdd` form an EXACT
group isomorphism `G ≃ 𝔤` (not merely the near-identity linear approximation the page describes for
the general non-abelian case) — this is a genuine instance of eq. (15)'s formula, not a strawman
simplification, since abelian Lie groups have exact (not merely locally-approximate) logarithms.
-/

private abbrev witnessSite := Fin 4
private abbrev witnessCenter := Fin 2

private noncomputable def witnessB : witnessCenter → Finset witnessSite
  | 0 => {0, 1}
  | 1 => {2, 3}

/-- Fine configuration: every site carries the rational value `x` (as an element of `ℚ`, embedded
via `Multiplicative.ofAdd`), and the coarse point carries `0`. Chosen so the weighted average has a
clean closed form to check. -/
private noncomputable def witnessΓ : witnessCenter → witnessSite → Multiplicative ℚ
  | _, x => Multiplicative.ofAdd (x.1 : ℚ)

private noncomputable def witnessUc : witnessCenter → Multiplicative ℚ :=
  fun _ => Multiplicative.ofAdd 0

/-- `averageAt` on the witness data at `c = 0`: `B(0) = {0,1}`, contour values `0` and `1`, `L=2,
d=1`, so the weighted sum is `2⁻¹·0 + 2⁻¹·1 = 1/2`, `U(c) = 0` (additively), giving `1/2`
overall. Computed in-kernel (explicit `Finset.sum` expansion + `norm_num` on `ℚ`, both
kernel-checked; no `native_decide`). -/
example :
    averageAt (G := Multiplicative ℚ) (𝔤 := ℚ)
      Multiplicative.toAdd Multiplicative.ofAdd witnessB 2 1 witnessΓ witnessUc 0
      = Multiplicative.ofAdd (1 / 2 : ℚ) := by
  unfold averageAt witnessB witnessΓ witnessUc
  dsimp only
  rw [show ({0, 1} : Finset witnessSite) = insert 0 {1} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-!
The degenerate-witness prosecution for `GaugeCovariant` (a constant averaging map that ignores the
fine configuration, blocked against a genuinely nontrivial gauge action) is executed in
`Balaban/Probes.lean` (`constantAverage_blocked`), not here — this file stays definitions-only.
-/

end AdalyFormal.Balaban
