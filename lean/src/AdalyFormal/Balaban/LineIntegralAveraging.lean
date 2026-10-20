/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoarseShiftCovariance
import AdalyFormal.Balaban.U1CommutingSquare
import AdalyFormal.Balaban.KernelSubspace

set_option autoImplicit false

/-!
# The FAITHFUL `Q_k` — CMP95 (1.18) WITH its line integral — and the (1.20) gradient intertwining

**Companion to `Balaban/U1AnchorRefutation.lean`** (read that module's docstring first). That module
proves the tree's `U=1` anchor statements are FALSE over `LatticeOperators.coarseRestrict`; THIS
module locates the defect constructively: `coarseRestrict` is NOT CMP95's `Q_k`, and the faithful
operator — built here — provably lacks the defect.

## Source, read from 300dpi page images (LAW-11; `compute/piece1_fourier/FINDINGS.md` [T6])

* CMP95 printed p.19, eq. (1.8): the block-averaging kernel acts on `A([x, x(c)])` where
  "`A(Γ) = Σ_{b⊂Γ} A_b` for arbitrary contour `Γ`" and "`x(c) = x + Le_μ`" — `[x, x(c)]` is the
  STRAIGHT SEGMENT of `L` fine bonds from `x` to `x + Le_μ`, and `A([x,x(c)])` is its additive line
  integral.
* CMP95 printed p.19, eq. (1.11) / p.20, eq. (1.18): `(Q_kA)_b = Σ_{x∈B^k(b₋)} η^{d+1}A([x,x(b)])`
  — the average of those line integrals: `η^{-d}` block sites × `η^{-1}` bonds per segment
  `= η^{-(d+1)}` terms against the `η^{d+1}` coefficient. **A true average** (value `c` on the
  constant field `c` — proved below, §5, and provably FALSE for the single-bond port, also §5).
* CMP95 printed p.19, eq. (1.13) / p.20, eq. (1.20): `Q_k(A − ∂λ) = Q_kA − ∂(Q_k'λ)` — `Q_k` maps
  fine gradients to EXACT coarse gradients of the site-average `Q_k'λ`. THE structural property the
  whole `U=1` sector rests on, proved here (§3) for the faithful operator, GENERALLY (any `L`, any
  aligned coarse point, any `ell ∣ L_μ+1` — not witness-only).

## What this module builds

1. **§1 `lineIntegralValue`** — `A([x, x + ell·e_μ]) = Σ_{j<ell} A(x+j·e_μ, μ)`, CMP95 (1.8) for
   the straight segment, with the telescoping identity on gradients:
   `lineIntegralValue ell (∂₀λ) x μ = λ(coarseShift x ell μ) − λ(x)`.
2. **§2 `lineCoarseRestrict`** — THE FAITHFUL `Q_k`, CMP95 (1.11)/(1.18): `(1/ell⁴)·Σ_{x∈B(y)}
   A([x, x+ell·e_μ])` (`d=3`: `η^{d+1} = 1/ell⁴` against `ell³·ell = ell⁴` terms).
3. **§3 THE (1.20) INTERTWINING, general** — `lineCoarseRestrict ell (∂₀λ) = (1/ell)·∂'(Q_ell'λ)`
   (coarse gradient of `KernelSubspace.coarseRestrictSite`), via `CoarseShiftCovariance.
   coarseShift_blockOf_eq_image` (LAW-19; the `1/ell` is the unit-fine-lattice dictionary constant
   for the coarse derivative, matching (1.13)'s explicit `L⁻¹`).
4. **§4 COARSE CURL VANISHES ON GRADIENT AVERAGES** — coarse gradients are coarse-curl-free
   (`coarseShift` commutation), hence `∂₁'(Q_ell^{faithful}(∂₀λ)) = 0` identically — the property
   whose FAILURE for the single-bond port is exactly what refutes the tree's anchor statements.
   **THE CONTRAST THEOREM**: on the IDENTICAL witness where the single-bond operator's coarse curl
   is `1/16 ≠ 0` (`U1CommutingSquare.coarseCurl_of_coarseRestrict_gradWitness_value`), the faithful
   operator's coarse curl is `0` — kernel-checked, side by side.
5. **§5 CALIBRATION / falsifiability** — (a) at `ell = 1` the faithful and single-bond operators
   AGREE (the port is correct exactly where `U1CurlCoercivity` PART B's true `ell=1` brick lives);
   (b) on the constant field the faithful operator returns the constant (a true average, per the
   source's `η^{d+1}` bookkeeping) while the single-bond operator returns HALF of it at
   `ell = 2` — the dropped `×ell` line-integral factor, exhibited numerically.

## Consequences (stated plainly)

* The `no_commuting_square_operator` obstruction ("Fourier unavoidable") does NOT transfer to the
  faithful `Q_k`: its witness is a pure gradient, and §4 kills every pure-gradient obstruction of
  that shape. Whether a full commuting square exists for the faithful operator (needing
  curl-free ⇒ gradient + harmonic, a discrete Hodge fact not in this tree) is left OPEN — named,
  not silently claimed.
* The repaired Piece-1 anchor should be restated over `lineCoarseRestrict` (or its CLM promotion)
  — a follow-up statement-level decision for the coordinator, since `HjMinimizer`/`CoarseCurl`/
  `U1Anchor` consume the single-bond operator throughout and are other lanes' write scope.

## What this module does NOT build (named residuals)

* The CLM/Hilbert-space promotion of `lineCoarseRestrict` and the rebuild of
  `HjMinimizer.deltaJQuadForm`'s constraint set over it (write-scope: `HjMinimizer.lean` is not
  this lane's).
* The `Γ_{c₋,x}`/`Γ_{x(c),c₊}` contour legs of the FULL (1.8) average (Bałaban's own (1.10)-(1.11)
  drop them under the axial gauge; this module builds (1.11)'s `Q`, the object the tree's
  `coarseRestrict` was always meant to port).
* The repaired anchor's momentum-space bound itself (the ORIGINAL Piece-1 mathematics, now to be
  attempted over the correct object).
-/

namespace AdalyFormal.Balaban.LineIntegralAveraging

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.KernelSubspace
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.CoarseShiftCovariance

variable {L : PeriodicLatticeExtent}

/-! ## §1. The straight-segment line integral, CMP95 (1.8) -/

/-- **`A([x, x + ell·e_μ]) := Σ_{j<ell} A(x + j·e_μ, μ)`** — CMP95 (1.8)'s additive line integral
`A(Γ) = Σ_{b⊂Γ} A_b` for the straight `ell`-bond segment `[x, x(b)]`, `x(b) = x + ell·e_μ`
(p.19: "`x(c) = x + Le_μ`"). -/
def lineIntegralValue (ell : ℕ) (A : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  ∑ j ∈ Finset.range ell, A ((fun z => periodicLatticeShift z μ)^[j] x, μ)

/-- **The telescoping identity**: the line integral of a gradient is the endpoint difference —
`(∂₀λ)([x, x+ell·e_μ]) = λ(x + ell·e_μ) − λ(x)`, the discrete fundamental theorem of calculus
along the segment. This is the mechanism (1.13)/(1.20) rest on. -/
theorem lineIntegralValue_gradValue (ell : ℕ) (lam : PeriodicLatticeSite L → ℝ)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    lineIntegralValue ell (gradValue lam) x μ = lam (coarseShift x ell μ) - lam x := by
  unfold lineIntegralValue coarseShift
  induction ell with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Function.iterate_succ_apply']
    simp only [gradValue]
    ring

#print axioms lineIntegralValue_gradValue

theorem lineIntegralValue_add (ell : ℕ) (A1 A2 : Bond L → ℝ) (x : PeriodicLatticeSite L)
    (μ : Fin 3) :
    lineIntegralValue ell (A1 + A2) x μ =
      lineIntegralValue ell A1 x μ + lineIntegralValue ell A2 x μ := by
  simp only [lineIntegralValue, Pi.add_apply]
  rw [← Finset.sum_add_distrib]

theorem lineIntegralValue_smul (ell : ℕ) (c : ℝ) (A : Bond L → ℝ) (x : PeriodicLatticeSite L)
    (μ : Fin 3) :
    lineIntegralValue ell (c • A) x μ = c * lineIntegralValue ell A x μ := by
  simp only [lineIntegralValue, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]

/-! ## §2. THE FAITHFUL `Q_k`, CMP95 (1.11)/(1.18) -/

/-- **`(Q_ell^{faithful} A)(b) := (1/ell⁴)·Σ_{x∈B(b₋)} A([x, x + ell·e_μ])`** — CMP95 (1.11)/
(1.18) with its line integral intact: `ell³` block sites, `ell` bonds per segment, `ell⁴` terms
against the `1/ell⁴ = η^{d+1}` coefficient (`d = 3`) — a genuine average (§5b). Same
`CoarseBond`-indexing as `LatticeOperators.coarseRestrict` (LAW-19), differing ONLY in the
line-integral factor that operator dropped. -/
noncomputable def lineCoarseRestrict (ell : ℕ) (A : Bond L → ℝ) (b : CoarseBond L ell) : ℝ :=
  (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf b.1.1 ell, lineIntegralValue ell A x b.2

theorem lineCoarseRestrict_add (ell : ℕ) (A1 A2 : Bond L → ℝ) (b : CoarseBond L ell) :
    lineCoarseRestrict ell (A1 + A2) b =
      lineCoarseRestrict ell A1 b + lineCoarseRestrict ell A2 b := by
  simp only [lineCoarseRestrict]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun x _ => lineIntegralValue_add ell A1 A2 x b.2

theorem lineCoarseRestrict_smul (ell : ℕ) (c : ℝ) (A : Bond L → ℝ) (b : CoarseBond L ell) :
    lineCoarseRestrict ell (c • A) b = c * lineCoarseRestrict ell A b := by
  simp only [lineCoarseRestrict]
  rw [show (∑ x ∈ blockOf b.1.1 ell, lineIntegralValue ell (c • A) x b.2) =
      c * ∑ x ∈ blockOf b.1.1 ell, lineIntegralValue ell A x b.2 by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => lineIntegralValue_smul ell c A x b.2]
  ring

#print axioms lineCoarseRestrict_add
#print axioms lineCoarseRestrict_smul

/-! ## §3. THE (1.20) INTERTWINING — general, not witness-only -/

/-- **CMP95 (1.13)/(1.20), faithfully and GENERALLY**: on any lattice `L`, at any aligned coarse
bond (`y ∈ CoarseLattice`, `ell ∣ L_μ+1`, `ell > 0`),
`(Q_ell^{faithful}(∂₀λ))(y,μ) = (1/ell)·[(Q_ell'λ)(y + ell·e_μ) − (Q_ell'λ)(y)]` — the coarse
gradient of the site block-average `Q_ell'λ = KernelSubspace.coarseRestrictSite` (LAW-19), with
the explicit `1/ell` dictionary constant matching (1.13)'s printed `L⁻¹`. Proof: telescope each
segment (§1), then reindex the shifted block sum via
`CoarseShiftCovariance.coarseShift_blockOf_eq_image` (LAW-19 — this handles torus wraparound
generally, the exact step `CovariantHjMinimizer`'s witness-only telescoping lemma named as its
missing generalization). -/
theorem lineCoarseRestrict_gradValue {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (lam : PeriodicLatticeSite L → ℝ) :
    lineCoarseRestrict ell (gradValue lam) (⟨y, hy⟩, μ) =
      (1 / (ell : ℝ)) *
        (coarseRestrictSite ell lam (coarseShift y ell μ) - coarseRestrictSite ell lam y) := by
  unfold lineCoarseRestrict coarseRestrictSite
  have hstep : (∑ x ∈ blockOf y ell, lineIntegralValue ell (gradValue lam) x μ) =
      (∑ x ∈ blockOf (coarseShift y ell μ) ell, lam x) - ∑ x ∈ blockOf y ell, lam x := by
    have h1 : (∑ x ∈ blockOf y ell, lineIntegralValue ell (gradValue lam) x μ) =
        (∑ x ∈ blockOf y ell, lam (coarseShift x ell μ)) - ∑ x ∈ blockOf y ell, lam x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => lineIntegralValue_gradValue ell lam x μ
    have h2 : (∑ x ∈ blockOf (coarseShift y ell μ) ell, lam x) =
        ∑ x ∈ blockOf y ell, lam (coarseShift x ell μ) := by
      rw [coarseShift_blockOf_eq_image hell hdvd hy]
      exact Finset.sum_image fun x _ x' _ h => coarseShift_injective ell μ h
    rw [h1, h2]
  rw [hstep]
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp

#print axioms lineCoarseRestrict_gradValue

/-! ## §4. Coarse curl vanishes on gradient averages — and THE CONTRAST THEOREM -/

/-- Coarse shifts in DIFFERENT directions commute — iterates of the commuting single fine steps
(`LatticeOperators.periodicLatticeShift_comm`). -/
theorem coarseShift_comm (y : PeriodicLatticeSite L) (ell : ℕ) {μ ν : Fin 3} (h : μ ≠ ν) :
    coarseShift (coarseShift y ell μ) ell ν = coarseShift (coarseShift y ell ν) ell μ := by
  have hc : Function.Commute (fun z : PeriodicLatticeSite L => periodicLatticeShift z ν)
      (fun z : PeriodicLatticeSite L => periodicLatticeShift z μ) := by
    intro z
    exact periodicLatticeShift_comm z h
  exact ((hc.iterate_left ell).iterate_right ell) y

#print axioms coarseShift_comm

/-- **Every coarse gradient is coarse-curl-free** — the four terms of `coarseCurlValue` telescope,
the residue being killed by `coarseShift_comm` (exactly mirroring the fine-lattice
`curlValue_gradValue`, LAW-19 one level up). -/
theorem coarseCurlValue_coarseGradient {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (f : PeriodicLatticeSite L → ℝ) (B : CoarseBond L ell → ℝ)
    (hB : ∀ b : CoarseBond L ell, B b = f (coarseShift b.1.1 ell b.2) - f b.1.1)
    (p : CoarsePlaquette L ell) :
    coarseCurlValue hdvd B p = 0 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  simp only [coarseCurlValue, hB]
  rw [coarseShift_comm p.1.1 ell hne]
  ring

#print axioms coarseCurlValue_coarseGradient

/-- **`∂₁'(Q_ell^{faithful}(∂₀λ)) = 0`, identically** — the structural property (1.20) forces:
gradient averages have NO coarse curl, at every coarse plaquette, for every `λ`, on every lattice
with `ell ∣ L_μ+1`, `ell > 0`. -/
theorem coarseCurlValue_lineCoarseRestrict_gradValue {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (lam : PeriodicLatticeSite L → ℝ)
    (p : CoarsePlaquette L ell) :
    coarseCurlValue hdvd (lineCoarseRestrict ell (gradValue lam)) p = 0 := by
  refine coarseCurlValue_coarseGradient hdvd
    (fun z => (1 / (ell : ℝ)) * coarseRestrictSite ell lam z)
    (lineCoarseRestrict ell (gradValue lam)) (fun b => ?_) p
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  rw [lineCoarseRestrict_gradValue hell (hdvd μ) hy lam]
  ring

#print axioms coarseCurlValue_lineCoarseRestrict_gradValue

/-- **THE CONTRAST THEOREM, kernel-checked side by side.** On the IDENTICAL pure-gauge witness
(`U1CommutingSquare.gradWitnessConfig = ∂₀(indicator at (1,0,0))`, witness lattice `4³`,
`ell = 2`) and at the IDENTICAL coarse plaquette:
* the tree's single-bond `coarseRestrict` has coarse curl `1/16 ≠ 0` — the value that refutes the
  `U=1` anchor statements (`U1AnchorRefutation.lean`);
* the faithful line-integral `lineCoarseRestrict` has coarse curl `0`.
The refutation is therefore an artifact of the unfaithful port, and Bałaban's own (1.67) target is
untouched by it. -/
theorem singleBond_vs_lineIntegral_contrast :
    coarseCurlValue witnessHdvd
        (LatticeOperators.coarseRestrict witnessEll U1CommutingSquare.gradWitnessConfig)
        (⟨witnessY, witnessY_coarse⟩, coarseWitnessDirs) = 1 / 16 ∧
      coarseCurlValue witnessHdvd
        (lineCoarseRestrict witnessEll U1CommutingSquare.gradWitnessConfig)
        (⟨witnessY, witnessY_coarse⟩, coarseWitnessDirs) = 0 := by
  constructor
  · exact U1CommutingSquare.coarseCurl_of_coarseRestrict_gradWitness_value
  · exact coarseCurlValue_lineCoarseRestrict_gradValue (by norm_num [witnessEll]) witnessHdvd
      U1CommutingSquare.gradWitnessLam
      (⟨witnessY, witnessY_coarse⟩, coarseWitnessDirs)

#print axioms singleBond_vs_lineIntegral_contrast

/-! ## §5. Calibration and falsifiability controls -/

/-- **(a) At `ell = 1` the faithful operator IS the tree's operator** — the port is correct
exactly at `ell = 1` (the one true `U1CurlCoercivity` PART B brick lives there, and stays
untouched by this module's findings). -/
theorem lineCoarseRestrict_one_eq_coarseRestrict (A : Bond L → ℝ) (b : CoarseBond L 1) :
    lineCoarseRestrict 1 A b = LatticeOperators.coarseRestrict 1 A b := by
  unfold lineCoarseRestrict LatticeOperators.coarseRestrict
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold lineIntegralValue
  simp

#print axioms lineCoarseRestrict_one_eq_coarseRestrict

/-- The witness block has `2³ = 8` sites (kernel-checked). -/
theorem witness_block_card :
    (blockOf witnessY witnessEll).card = 8 := by decide

/-- **(b₁) The faithful operator is a TRUE AVERAGE**: on the constant field `1` it returns `1`
(at the concrete witness coarse bond; `8` block sites × `2` bonds per segment × `1` against
`1/16`) — matching the source's `η^{d+1}`-per-`η^{-(d+1)}`-terms bookkeeping. -/
theorem lineCoarseRestrict_const_witness :
    lineCoarseRestrict witnessEll (fun _ => (1 : ℝ))
      (⟨witnessY, witnessY_coarse⟩, 0) = 1 := by
  unfold lineCoarseRestrict lineIntegralValue
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [witness_block_card]
  unfold witnessEll
  norm_num

/-- **(b₂) The single-bond operator is NOT an average**: on the SAME constant field `1` at the
SAME coarse bond it returns `1/2` — off by exactly the dropped line-integral factor `ell = 2`.
This is the numerical fingerprint of the port defect, isolated from all curl/gauge structure. -/
theorem coarseRestrict_const_witness :
    LatticeOperators.coarseRestrict witnessEll (fun _ => (1 : ℝ))
      (⟨witnessY, witnessY_coarse⟩, 0) = 1 / 2 := by
  unfold LatticeOperators.coarseRestrict
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [witness_block_card]
  unfold witnessEll
  norm_num

#print axioms witness_block_card
#print axioms lineCoarseRestrict_const_witness
#print axioms coarseRestrict_const_witness

/-! ## §6. Hilbert-space (CLM) promotion — the object the repaired anchor statement needs, ready
for the follow-up lane (OPS-10: residual attempted in-pass rather than spawned). Mirrors
`LatticeOperators.coarseRestrictCLM`'s exact promotion pattern (LAW-19). -/

/-- The faithful `Q_ell` as a `LinearMap` on raw function spaces. -/
noncomputable def lineCoarseRestrictLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (Bond L → ℝ) →ₗ[ℝ] (CoarseBond L ell → ℝ) where
  toFun A := lineCoarseRestrict ell A
  map_add' A1 A2 := funext fun b => lineCoarseRestrict_add ell A1 A2 b
  map_smul' c A := funext fun b => lineCoarseRestrict_smul ell c A b

/-- The faithful `Q_ell`, transported to the Hilbert-space layer. -/
noncomputable def lineCoarseRestrictLMH (L : PeriodicLatticeExtent) (ell : ℕ) :
    BondSpace L →ₗ[ℝ] CoarseBondSpace L ell :=
  (coarseBondEquiv L ell).symm.toLinearMap.comp
    ((lineCoarseRestrictLM L ell).comp (bondEquiv L).toLinearMap)

/-- **The faithful `Q_ell` as a genuine `ContinuousLinearMap`** — the drop-in replacement for
`LatticeOperators.coarseRestrictCLM` in a repaired `HjMinimizer`/`U1Anchor` chain. -/
noncomputable def lineCoarseRestrictCLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    BondSpace L →L[ℝ] CoarseBondSpace L ell :=
  LinearMap.toContinuousLinearMap (lineCoarseRestrictLMH L ell)

/-- Transport `rfl`-lemma, same pattern as `HjMinimizer.coarseRestrictCLM_apply` (LAW-19). -/
theorem lineCoarseRestrictCLM_apply (L : PeriodicLatticeExtent) (ell : ℕ) (A : BondSpace L) :
    coarseBondEquiv L ell (lineCoarseRestrictCLM L ell A) =
      lineCoarseRestrict ell (bondEquiv L A) := rfl

#print axioms lineCoarseRestrictLM
#print axioms lineCoarseRestrictCLM
#print axioms lineCoarseRestrictCLM_apply

end AdalyFormal.Balaban.LineIntegralAveraging
