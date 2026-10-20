/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKFull

set_option autoImplicit false

/-!
# Normalization audit — is `deltaKQuadFormCorrected` consistently normalized?

**Task**: adjudicate a claim raised in a Sol de-correlated gate
(`compute/sol_domination_gate/SOL_VERDICT.md` §3) that `DeltaKFull.deltaKQuadFormCorrected :=
dstarDQuadForm U A + deltaPrimeQuadFormTransported U A` sums two summands carrying DIFFERENT trace
normalizations, and that fixing this changes the witness value from `-4` to `0`.

## Q1 — is there an inconsistency in the Lean, as written?

**YES.** Traced term by term, with line numbers, on this HEAD (`bc07f265`):

* `SuTwoInner.hsInner X Y := -(1/2 : ℝ) * (Matrix.trace (X * Y)).re`
  (`SuTwoInner.lean:87-89`). Its own docstring derives the `-(1/2)` as a PRODUCT of two factors
  (`SuTwoInner.lean:45-46`): `(-1)` from the `φ:X↦iX` Hermitian-transport, **times** `(1/2)` from
  Bałaban's OWN trace normalization `tr 1 = 1` (image-verified quote, `SuTwoInner.lean:32-33`,
  reproduced at 300dpi below in Q2). So `hsInner` bakes in BOTH the sign correction AND the
  `tr = (1/2)Tr` (for `N=2`) normalization correction, simultaneously, by construction.
* `CovariantHj.dstarDQuadForm U A := covPlaqInner (curl U A) (curl U A)` (`CovariantHj.lean:163-166`)
  and `covPlaqInner`/`covBondInner` (`CovariantHj.lean:133-138`) are built ENTIRELY from `hsInner`
  (`∑ p, hsInner (A p) (B p)`) — no raw `Matrix.trace` anywhere in the `dstarDQuadForm` chain. So
  `dstarDQuadForm` carries hsInner's normalization throughout.
* `DeltaPrime.deltaPrimeFirstTerm`/`deltaPrimeSecondTerm` (`DeltaPrime.lean:168-180`) are built from
  RAW, UNNORMALIZED `Matrix.trace` directly (`(Matrix.trace (... )).re`), with **no `1/2` factor
  anywhere** and no route through `hsInner`/`covPlaqInner`/`covBondInner`.
* `DeltaPrime.deltaPrimeFirstTermTransported`/`SecondTermTransported` (`DeltaPrime.lean:962-990`)
  and the proved pin `deltaPrimeQuadFormTransported_eq_neg` (`DeltaPrime.lean:1052-1064`) apply
  ONLY the `φ`-transport SIGN correction (`i² = -1`, i.e. literal `-1×`), never a `1/2` factor —
  confirmed by reading the actual proof terms, which are `rw [..., neg_mul, Matrix.trace_neg,
  Complex.neg_re]`-style sign manipulations with no `(1/2 : ℝ)` literal anywhere in the file's `Δ′`
  chain (grepped: the ONLY `1/2` literals in `DeltaPrime.lean` are in `reHolonomy`/`imHolonomy`,
  §1, which are Bałaban's OWN `(1/2)(U+U⁻¹)`/`(1/2i)(U-U⁻¹)` formulas from eq. (3.7), not a
  trace-normalization factor).
* Hence `DeltaKFull.deltaKQuadFormCorrected U A := dstarDQuadForm U A +
  deltaPrimeQuadFormTransported U A` (`DeltaKFull.lean:206-210`) sums a `-(1/2)`-normalized term
  (sign AND scale corrected) with a term that is ONLY sign-corrected (scale still raw/unnormalized,
  a factor of `2` too large relative to `dstarDQuadForm`'s own convention). **The two summands are
  inconsistently normalized as literally written.** `DeltaKFull.lean`'s own §0 derivation (its
  lines 53-71) explicitly re-derives and confirms the `hsInner`-side of this (`"the final -½ factor
  is Bałaban's own trace normalization, tr = ½Tr for N=2, immaterial to the SIGN question this
  section asks"`) but its own §0 argument is scoped ONLY to the SIGN question, and the file's own
  parenthetical concedes the factor is being set aside, not resolved.

Sol is right; the earlier `DeltaKFull.lean` §0 sign-only derivation is not wrong about the sign, but
incomplete about the normalization.

## Q2 — what does the source require?

CMP99b p.392 (rendered fresh at 300dpi in this pass, `compute/carrier_audit/renders/CMP99b_p392-04.png`,
header "392 / T. Balaban" visually confirmed), VERBATIM, top of page:

> "by `X · Y = tr XY`. Let us recall that the trace is normalized, i.e., `tr 1 = 1`."

immediately followed, same page, by eq. (3.10) itself:

> `⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ′A⟩`
> `⟨A,Δ′A⟩ = Σ_{p⊂T_η} η^d tr((D¹_U A)(p))² η⁻² (Re U(∂p) - 1)`
> `  + tr Σ_{b1,b2⊂∂(p)_z, b1≺b2} i[A′(b1),A′(b2)] η⁻² Im U(∂p).`               (3.10)

**Both terms of `Δ′` use the SAME symbol `tr`** — the normalized trace defined two lines above,
on the SAME page, for the SAME reason it is used in `⟨A,D*DA⟩`. There is no second, unnormalized
`Tr` anywhere on this page; Bałaban never writes `Δ′` with a different trace than `D*D`. Since
`⟨A,ΔA⟩` is a single sum `⟨A,D*DA⟩ + ⟨A,Δ′A⟩` under one hermitian operator `Δ`, and both pieces use
the identical `tr`, **consistency requires the SAME normalization factor in both summands.** For
`N = 2`, `tr = (1/2)Tr` (raw `Matrix.trace`) — the same factor `hsInner` already applies.

No ambiguity: the page image settles this without qualification. (The `su(2)` generators `iσ_a`
satisfy `Tr(iσ_a·iσ_b) = -2δ_ab`, so `-(1/2)Tr` — Bałaban's own normalized `-tr`, transported by
`φ` — makes them orthonormal; this is an independent corroboration already exploited by
`SuTwoInner.lean`'s `hsInner_e1_e1`/`hsInner_e2_e2`/`hsInner_e3_e3`.)

## Q3 — recomputed value

Building the CONSISTENTLY-normalized transported `Δ′` (i.e. the `Δ′` sign-and-scale correction that
actually matches `hsInner`'s own factor) as `(1/2) * deltaPrimeQuadFormTransported` (proved below,
`deltaPrimeQuadFormNormalizedTransported_eq_half_transported`, an algebraic identity, not an
assumption), and reproving the FIRST summand's witness value from scratch in this file
(`dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four`, mirroring the technique already banked for
`Δ′` at `DeltaPrime.lean` §6-§10, using ONLY already-banked lemmas from `DeltaPrime.lean`/
`CovariantHj.lean`, no new axiom, no `sorry`):

```
dstarDQuadForm witnessU deltaWitnessConfig                        = 4
deltaPrimeQuadFormTransported witnessU deltaWitnessConfig          = -8   (already banked)
deltaKQuadFormCorrected witnessU deltaWitnessConfig                = 4 + (-8)       = -4   (misnormalized, current tree)
deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig      = 4 + (1/2)(-8)  = 0    (source-consistent)
```

**Q3 answer: the correctly-normalized total is `0`, not `-4`.** Sol's claim is CONFIRMED, by direct
Lean re-derivation, both algebraically (the general identity
`deltaKQuadFormNormalizedCorrected U A = dstarDQuadForm U A + (1/2)*deltaPrimeQuadFormTransported U A`,
proved for ALL `U`, `A`) and numerically at the witness (theorem
`deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero` below, `#print axioms`-clean).

**This is NOT the same finding as `DeltaKFull.lean`'s own §0 correction** (which fixed only the
`φ`-transport SIGN, `deltaPrimeQuadForm → deltaPrimeQuadFormTransported`, going from `Δ=D*D+Δ′_raw`
at `+8` on `Δ′` to `Δ=D*D+Δ′_transported` at `-8` on `Δ′`, landing at `-4` overall). This file adds
a SECOND, independent correction (the `1/2` normalized-trace factor `hsInner` already carries but
raw `Matrix.trace` in `Δ′` never picked up), landing at `0`.

## What this file does NOT resolve

* It does not edit `DeltaPrime.lean`/`DeltaKFull.lean`/`TheLemma.lean` (write-scope discipline;
  multiple banked results consume `deltaKQuadFormCorrected` as currently defined — see the
  propagation section of `NORMALIZATION_AUDIT.md`).
* It does not re-derive whether `0` (an EXACT cancellation on this one witness family) generalizes
  to positivity/nonnegativity for ALL `U`/`A` — that is a strictly larger claim than this file
  proves. `0` at ONE non-flat witness refutes the CLAIM "this witness proves the corrected form
  goes negative"; it does not itself prove `deltaKQuadFormNormalizedCorrected ≥ 0` everywhere.
* It does not decide which of `deltaKQuadFormCorrected` (current tree definition) or
  `deltaKQuadFormNormalizedCorrected` (this file) is the object later files should consume — that
  is a cross-file, coordinator-level decision (`DeltaKFull.lean:1101-1115`'s own precedent for how
  such decisions are made, extended here to the second factor).
-/

namespace AdalyFormal.Balaban.NormalizationAudit

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.DeltaKFull

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the consistently-normalized `Δ′`, built term-by-term from the raw pieces -/

/-- Bałaban's `Δ′` FIRST term, carrying the SAME `(1/2)` normalized-trace factor `hsInner` already
applies to `dstarDQuadForm` (Q2). Defined from the RAW term, not assumed. -/
noncomputable def deltaPrimeFirstTermNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  (1 / 2 : ℝ) * deltaPrimeFirstTerm U A p

/-- Bałaban's `Δ′` SECOND term, same normalization correction. -/
noncomputable def deltaPrimeSecondTermNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  (1 / 2 : ℝ) * deltaPrimeSecondTerm U A p

noncomputable def deltaPrimePlaqTermNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  deltaPrimeFirstTermNormalized U A p + deltaPrimeSecondTermNormalized U A p

theorem deltaPrimePlaqTermNormalized_eq_half
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    deltaPrimePlaqTermNormalized U A p = (1 / 2 : ℝ) * deltaPrimePlaqTerm U A p := by
  unfold deltaPrimePlaqTermNormalized deltaPrimeFirstTermNormalized
    deltaPrimeSecondTermNormalized deltaPrimePlaqTerm
  ring

#print axioms deltaPrimePlaqTermNormalized_eq_half

/-- **`⟨A,Δ′A⟩`, consistently normalized** (Q2's answer applied throughout, untransported). -/
noncomputable def deltaPrimeQuadFormNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, deltaPrimePlaqTermNormalized U A p

/-- **The normalized `Δ′` is EXACTLY half the raw (misnormalized) `Δ′`** — a clean algebraic
identity, proved (not assumed), for ALL `U`, `A`. This is the load-bearing lemma of this file: it
converts "reproduce the corrected numeral" into a one-line rewrite anywhere `deltaPrimeQuadForm`'s
witness value is already banked. -/
theorem deltaPrimeQuadFormNormalized_eq_half
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeQuadFormNormalized U A = (1 / 2 : ℝ) * deltaPrimeQuadForm U A := by
  unfold deltaPrimeQuadFormNormalized deltaPrimeQuadForm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => deltaPrimePlaqTermNormalized_eq_half U A p)

#print axioms deltaPrimeQuadFormNormalized_eq_half

/-- The `φ`-transported (sign-corrected), consistently-normalized `Δ′`. -/
noncomputable def deltaPrimeQuadFormNormalizedTransported
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  -deltaPrimeQuadFormNormalized U A

/-- **`deltaPrimeQuadFormNormalizedTransported = (1/2) * deltaPrimeQuadFormTransported`** — the
KEY relative-normalization fact this dispatch was launched to settle, stated once and for all as a
kernel-checked theorem, general in `U`/`A`. -/
theorem deltaPrimeQuadFormNormalizedTransported_eq_half_transported
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeQuadFormNormalizedTransported U A =
      (1 / 2 : ℝ) * deltaPrimeQuadFormTransported U A := by
  unfold deltaPrimeQuadFormNormalizedTransported
  rw [deltaPrimeQuadFormNormalized_eq_half, deltaPrimeQuadFormTransported_eq_neg]
  ring

#print axioms deltaPrimeQuadFormNormalizedTransported_eq_half_transported

/-! ## §2 — `dstarDQuadForm witnessU deltaWitnessConfig = 4`, reproved fresh in this file

The tree's own `DeltaKFull.lean`/`DeltaPrime.lean` never states this numeral (checked: `grep`
returns no occurrence of a proved `dstarDQuadForm ... deltaWitnessConfig ... = 4` anywhere under
`formal/AdalyFormal/`). It IS proved in a Sol evidence snapshot
(`compute/sol_stmt_gate/evidence/FreshAttackFull.lean:667-699`,
`dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four`, `#print axioms`-clean there per
`compute/sol_stmt_gate/evidence/fresh_attack.literal.txt:56`), which is REPRODUCED HERE
independently, against the main tree's own current `DeltaPrime.lean`/`CovariantHj.lean` (not
against that snapshot), using only lemmas already banked in those two files. -/

/-- **General vanishing**: `curlValueCovariant` is `0` at a plaquette whose 4 boundary bonds are
all `0` — mirrors the internal `hcurl` step already proved inline inside
`DeltaPrime.deltaPrimePlaqTerm_eq_zero_of_bonds_zero` (`DeltaPrime.lean:421-424`), extracted here as
a standalone reusable fact about `curlValueCovariant` alone (no `Δ′`-specific content). -/
theorem curl_eq_zero_of_bonds_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h1 : A (p.1, p.2.1.1) = 0) (h2 : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0)
    (h3 : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) (h4 : A (p.1, p.2.1.2) = 0) :
    curlValueCovariant U A p = 0 := by
  unfold curlValueCovariant
  rw [h1, h2, h3, h4]
  simp

#print axioms curl_eq_zero_of_bonds_zero

/-- **Away from the four plaquettes touching the support bond, `deltaWitnessConfig`'s curl is
zero**, at `witnessU` — mirrors `DeltaPrime.deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero`'s own
proof structure (`DeltaPrime.lean:442-465`) exactly, specialized to `curlValueCovariant` alone. -/
theorem curl_witnessU_deltaWitnessConfig_eq_zero
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2)
    (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    curlValueCovariant witnessU deltaWitnessConfig p = 0 := by
  apply curl_eq_zero_of_bonds_zero
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp1 h
    · exact hp2 h
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact hp3 h
    · exact hp4 h
  · apply deltaWitnessConfig_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)

#print axioms curl_witnessU_deltaWitnessConfig_eq_zero

/-- **The `D*D` term at the tree's own witness: `dstarDQuadForm witnessU deltaWitnessConfig = 4`.**
Four support plaquettes each contribute `hsInner(±suTwoWitness, ±suTwoWitness) = 1`; every other
plaquette contributes `0` (previous theorem). -/
theorem dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four :
    dstarDQuadForm witnessU deltaWitnessConfig = 4 := by
  unfold dstarDQuadForm covPlaqInner
  have hS : ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hzero : ∀ p ∈ (Finset.univ :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)),
      p ∉ ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
        Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) →
      hsInner (curlValueCovariant witnessU deltaWitnessConfig p)
        (curlValueCovariant witnessU deltaWitnessConfig p) = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    rw [curl_witnessU_deltaWitnessConfig_eq_zero hp.1 hp.2.1 hp.2.2.1 hp.2.2.2,
      hsInner_zero_zero]
  rw [← Finset.sum_subset hS hzero]
  have hne1 : witnessPlaquette ≠ myWitnessPlaquette2 := by decide
  have hne2 : witnessPlaquette ≠ p3 := by decide
  have hne3 : witnessPlaquette ≠ p4 := by decide
  have hne4 : myWitnessPlaquette2 ≠ p3 := by decide
  have hne5 : myWitnessPlaquette2 ≠ p4 := by decide
  have hne6 : p3 ≠ p4 := by decide
  rw [Finset.sum_insert (by simp [hne1, hne2, hne3]),
    Finset.sum_insert (by simp [hne4, hne5]), Finset.sum_pair hne6,
    curl_witnessU_witnessPlaquette, curl_witnessU_myWitnessPlaquette2,
    curl_witnessU_p3, curl_witnessU_p4, hsInner_suTwoWitness_self]
  have hn : hsInner (-suTwoWitness) (-suTwoWitness) = 1 := by
    rw [show -suTwoWitness = (-1 : ℝ) • suTwoWitness by module,
      hsInner_smul_smul, hsInner_suTwoWitness_self]
    norm_num
  rw [hn]
  norm_num

#print axioms dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four

/-! ## §3 — the two assemblies at the witness, side by side -/

/-- **The CURRENT tree's `deltaKQuadFormCorrected` at the witness: `-4`** (misnormalized reading,
stated here for direct side-by-side comparison; this is NOT a new finding — it is a reproduction of
what `compute/kimi_stmt_gate/KIMI_STMT_GATE.md`/`compute/sol_stmt_gate/SOL_STMT_GATE.md` already
banked, re-derived fresh here against the CURRENT tree state). -/
theorem deltaKQuadFormCorrected_witnessU_deltaWitnessConfig_eq_neg_four :
    deltaKQuadFormCorrected witnessU deltaWitnessConfig = -4 := by
  unfold deltaKQuadFormCorrected
  rw [dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four,
    deltaPrimeQuadFormTransported_witnessU_eq]
  norm_num

#print axioms deltaKQuadFormCorrected_witnessU_deltaWitnessConfig_eq_neg_four

/-- **The consistently-normalized `Δ_k(U)` quadratic form** — `dstarDQuadForm` plus the
CONSISTENTLY-normalized transported `Δ′` (§1), i.e. this file's answer to Q1-Q2. -/
noncomputable def deltaKQuadFormNormalizedCorrected
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  dstarDQuadForm U A + deltaPrimeQuadFormNormalizedTransported U A

/-- **General identity**: the normalized assembly equals `dstarDQuadForm + (1/2) *
deltaPrimeQuadFormTransported`, for ALL `U`, `A` — makes the relative factor of `2` between the
current tree's `deltaKQuadFormCorrected` and this file's `deltaKQuadFormNormalizedCorrected`
completely explicit and mechanically checkable. -/
theorem deltaKQuadFormNormalizedCorrected_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaKQuadFormNormalizedCorrected U A =
      dstarDQuadForm U A + (1 / 2 : ℝ) * deltaPrimeQuadFormTransported U A := by
  unfold deltaKQuadFormNormalizedCorrected
  rw [deltaPrimeQuadFormNormalizedTransported_eq_half_transported]

#print axioms deltaKQuadFormNormalizedCorrected_eq

/-- **THE HEADLINE RESULT — Q3, answered.** At the tree's own non-flat regular witness, the
consistently-normalized `Δ_k(U)` quadratic form is exactly `0`, NOT `-4`. This is the decisive
computation this dispatch was launched to settle. -/
theorem deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero :
    deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0 := by
  rw [deltaKQuadFormNormalizedCorrected_eq, dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four,
    deltaPrimeQuadFormTransported_witnessU_eq]
  norm_num

#print axioms deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero

/-- **Sanity check the correction is not vacuous**: the two assemblies genuinely differ at the
witness (`-4 ≠ 0`), confirming this file's normalization fix is substantive, not a relabelling. -/
theorem deltaKQuadFormNormalizedCorrected_ne_deltaKQuadFormCorrected_at_witness :
    deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig ≠
      deltaKQuadFormCorrected witnessU deltaWitnessConfig := by
  rw [deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero,
    deltaKQuadFormCorrected_witnessU_deltaWitnessConfig_eq_neg_four]
  norm_num

#print axioms deltaKQuadFormNormalizedCorrected_ne_deltaKQuadFormCorrected_at_witness

end AdalyFormal.Balaban.NormalizationAudit
