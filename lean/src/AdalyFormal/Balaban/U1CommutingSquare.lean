/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoarseCurl

set_option autoImplicit false

/-!
# WAVE 1 / LANE A-2: the elementary commuting-square route to Piece 1 (`γ₀=1`) — REFUTED

**Dispatch** (`GOAL_LEMMA.md` §3 Piece 1, retrying Lane A's Fourier route via an elementary
alternative): does the "commuting square" `∂₁ ∘ Q_k = M ∘ ∂` hold as an EXACT operator identity,
for SOME linear `M : PlaquetteSpace L →ₗ[ℝ] CoarsePlaquetteSpace L ell`, so that
`‖∂₁B‖ = ‖∂₁(Q_kH_kB)‖ = ‖M(∂H_kB)‖ ≤ ‖∂H_kB‖` would follow elementarily (via `‖M‖≤1`) and close
`⟨B,Δ_kB⟩ = ‖∂H_kB‖² ≥ ‖∂₁B‖²`, i.e. `γ₀=1`, with NO Fourier/momentum-space computation?

## THE ANSWER: NO — decisively, and more strongly than the dispatch anticipated

The dispatch's own fallback anticipated two outcomes: (a) `M` exists and is a manifest averaging
operator (⟹ `‖M‖≤1` by convexity, route closes), or (b) the NATURAL candidate `M =
coarsePlaquetteRestrictCLM` fails the identity (⟹ Fourier likely unavoidable). **What this module
proves is STRONGER than (b): NO linear map `M` whatsoever — not merely the natural averaging
candidate, but ANY linear map, with ANY norm, ANY sign structure — can satisfy the exact identity
`∂₁∘Q_k = M∘∂` on all of `BondSpace L`.** This is a pure finite-dimensional linear-algebra fact:
`M` exists satisfying `∂₁∘Q_k = M∘∂` iff `ker(∂) ⊆ ker(∂₁∘Q_k)`, and this module exhibits an
EXPLICIT vector in `ker(∂) \ ker(∂₁∘Q_k)` — a "pure gauge" (exact/gradient) bond configuration
`v = ∂₀λ` on the shared witness lattice, for which `∂v = 0` identically (the general, already-proved
"curl of a gradient vanishes" fact, `LatticeOperators.curlCLM_comp_gradCLM_eq_zero`), while
`∂₁(Q_k v) = 1/16 ≠ 0` at an explicit coarse plaquette (kernel-checked, exact rational arithmetic).

**This kills the elementary route outright, and independently corroborates two other pieces of
evidence already in this tree:**
1. `CoarseCurl.lean` §6 already refuted the ONE NATURAL candidate `M = coarsePlaquetteRestrictCLM`
   on a DIFFERENT (non-exact) witness bond configuration (`-1/16 ≠ 0`). This module's finding
   subsumes and strengthens that: it is not merely that the natural candidate happens to fail, but
   that failure is UNAVOIDABLE for every candidate, because the obstruction is already visible on
   the KERNEL of `∂` alone (where EVERY candidate `M` is forced to agree: `M(0)=0`).
2. CMP95 printed p.29, eq. (1.65)-(1.67) (`corpus/mathpix/balaban_CMP95_1984_propagators_I/
   normalized/p29.md`, read directly for this dispatch): Bałaban's own derivation of `γ₀‖∂₁B,∂₁B⟩ ≤
   ⟨B,Δ_kB⟩ ≤ γ₁⟨∂₁B,∂₁B⟩` (1.67) goes through the FULL momentum-space representation (1.66) — a
   Fourier integral over the reciprocal lattice with an explicit symbol `φ_μ(p')`, `Δ₀(p')`, bounded
   above/below by `d`-only constants — with NO commuting-square argument stated or used anywhere on
   this page or its neighbors. The source's own proof strategy is exactly the "heavy Fourier"
   machinery Lane A found necessary (`compute/lane_A_u1momentum/BUILD.md`); this module now shows
   WHY an elementary shortcut cannot exist, not merely that no one has found one.

## Why the naive route fails, made precise (not just "it happens to fail on some input")

`Q_k` averages a bond field over an `ell`-cube TRANSVERSE to the bond's own direction (a "slab"
average, CMP95 eq. 1.18's own `η^{d+1}` normalization). `∂₁` differences ADJACENT bond values
around a plaquette loop using the `ell`-fold coarse shift (forced by `CoarseBondSpace`'s own
indexing, `CoarseCurl.lean`'s module docstring). Composing them, `∂₁(Q_k A)` at a coarse plaquette
compares SLAB AVERAGES of `A` taken over four DIFFERENT, generally non-overlapping `ell`-cubes
(one per side of the coarse plaquette) — a fundamentally different combinatorial object from `∂A`
telescoped over the coarse plaquette's boundary path, which would use `A`'s values along a single
one-fine-lattice-wide loop. For a general (or even an exact/pure-gauge) `A`, there is no reason
these two objects should agree, and for the witness built below, they provably do not.

## What this module builds

1. `gradWitnessLam`/`gradWitnessConfig` (§1) — the concrete pure-gauge witness `v = ∂₀λ`, `λ` an
   indicator at `CoarseCurl.curlWitnessSite` (LAW-19 reuse of an already-audited witness point).
2. `sum_gradWitnessLam_plain`/`sum_gradWitnessLam_shift` (§2) — general block-sum evaluation
   lemmas for a single-point indicator, reusable machinery (not specific to this witness's
   particular geometry beyond the shift direction).
3. `preWitnessSite1`/`preWitnessSite1_shift` (§3) — the second concrete site needed (the
   direction-`1` shift-preimage of `curlWitnessSite`).
4. `coarseRestrict_gradWitness_eq` (§4) — the general block-average value formula for `Q_k v`,
   parametrized by base site and direction.
5. `coarseCurl_of_coarseRestrict_gradWitness_value` (§5) — **THE COMPUTATION**: `∂₁(Q_kv)` at the
   witness plaquette equals `1/16`, exact rational, kernel-checked.
6. `no_commuting_square_valueLevel` (§6) — **THE VALUE-LEVEL IMPOSSIBILITY THEOREM**: no linear map
   between the raw plaquette-indexed function spaces can satisfy the commuting square, for ANY
   witness lattice/`ell`/tileability instance sharing this module's concrete configuration.
7. `no_commuting_square_operator` (§7) — **THE OPERATOR-LEVEL (Hilbert-space) COROLLARY**: no
   `ContinuousLinearMap M : PlaquetteSpace L →L[ℝ] CoarsePlaquetteSpace L ell` satisfies
   `∂₁∘Q_k = M∘∂`, directly answering the dispatch's "is `M` a manifest contraction" question with
   "no `M` of any kind exists."

## What this module does NOT claim

* This does NOT show `γ₀=1` is false, nor that Piece 1 is false — only that THIS PARTICULAR proof
  strategy (a universal commuting-square factorization) cannot work. A weaker, `B`-dependent
  factorization restricted to `range(H_k)` alone is not ruled out by this module, but constructing
  one would require exactly the structural knowledge of `H_k`'s range that only the momentum-space
  computation (CMP95 1.60-1.67) supplies — i.e., it collapses back to the Fourier route, not an
  independent elementary shortcut.
* This module does NOT build any new coarse-curl/coarse-restrict machinery — it consumes
  `CoarseCurl.lean`'s `coarseCurlCLM`/`coarseCurlValue` and `LatticeOperators.lean`'s
  `gradCLM`/`curlCLM`/`coarseRestrictCLM` exactly as built (LAW-19).
-/

namespace AdalyFormal.Balaban.U1CommutingSquare

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CoarseCurl
-- `open AdalyFormal.Balaban.HjMinimizer` REMOVED (substrate-wiring lane, 2026-07-24): this file's
-- only use of that namespace was `coarseRestrictCLM_apply`, relocated to `LatticeOperators.lean`
-- (its true home, next to `coarseRestrictCLM`'s own definition) to break an import cycle
-- (`HjMinimizer → LineIntegralAveraging → CoarseShiftCovariance → CoarseCurl → HjMinimizer` via
-- this file's own transitive `CoarseCurl` import). `coarseRestrictCLM_apply` below now resolves
-- via the already-open `LatticeOperators` namespace, unqualified, unchanged in meaning.

/-! ## §1. The pure-gauge witness `v = ∂₀λ` -/

/-- **`λ`, an indicator at `CoarseCurl.curlWitnessSite` (`= (1,0,0)` on the witness lattice,
already-audited point, LAW-19 reuse).** -/
noncomputable def gradWitnessLam : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ :=
  fun x => if x = CoarseCurl.curlWitnessSite then 1 else 0

/-- **`v := ∂₀λ`, the pure-gauge (exact) bond configuration.** -/
noncomputable def gradWitnessConfig : Bond AdmissibleSubspace.witnessL → ℝ :=
  gradValue gradWitnessLam

/-- **`v` is genuinely pure gauge: `∂₁v = 0` at EVERY plaquette**, general (not a spot check),
directly from the already-proved exactness identity `curlValue_gradValue` — no computation needed
here. -/
theorem gradWitnessConfig_curl_eq_zero
    (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL) :
    curlValue gradWitnessConfig p = 0 :=
  curlValue_gradValue gradWitnessLam p

#print axioms gradWitnessConfig_curl_eq_zero

/-! ## §2. General block-sum evaluation for a single-point indicator -/

/-- **The "plain" sum of `gradWitnessLam` over a Finset `S`** collapses to a membership test
(`Finset.sum_ite_eq'`). -/
theorem sum_gradWitnessLam_plain (S : Finset (PeriodicLatticeSite AdmissibleSubspace.witnessL)) :
    (∑ x ∈ S, gradWitnessLam x) = if CoarseCurl.curlWitnessSite ∈ S then (1 : ℝ) else 0 := by
  unfold gradWitnessLam
  exact Finset.sum_ite_eq' S CoarseCurl.curlWitnessSite (fun _ => (1 : ℝ))

/-- **The "shifted" sum**, `∑_{x∈S} λ(shift_μ x)`, collapses to a membership test on the
`μ`-shift-PREIMAGE `pre` of `curlWitnessSite`, given `pre` supplied with its defining shift
equation. `periodicLatticeShift_injective` (`CoarseCurl.lean`, LAW-19 reuse) is what makes `pre`
the UNIQUE such point, hence what makes the "no other `x` can also hit `curlWitnessSite`" step
valid. -/
theorem sum_gradWitnessLam_shift (S : Finset (PeriodicLatticeSite AdmissibleSubspace.witnessL))
    (μ : Fin 3) (pre : PeriodicLatticeSite AdmissibleSubspace.witnessL)
    (hpre : periodicLatticeShift pre μ = CoarseCurl.curlWitnessSite) :
    (∑ x ∈ S, gradWitnessLam (periodicLatticeShift x μ)) = if pre ∈ S then (1 : ℝ) else 0 := by
  by_cases h : pre ∈ S
  · rw [if_pos h]
    rw [Finset.sum_eq_single pre]
    · unfold gradWitnessLam
      rw [hpre, if_pos rfl]
    · intro x _ hne
      unfold gradWitnessLam
      rw [if_neg]
      intro heq
      exact hne (CoarseCurl.periodicLatticeShift_injective μ (heq.trans hpre.symm))
    · intro hcontra
      exact absurd h hcontra
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x hx
    unfold gradWitnessLam
    rw [if_neg]
    intro heq
    apply h
    have hxeq : x = pre := CoarseCurl.periodicLatticeShift_injective μ (heq.trans hpre.symm)
    rwa [hxeq] at hx

#print axioms sum_gradWitnessLam_plain
#print axioms sum_gradWitnessLam_shift

/-! ## §3. The second concrete site: the direction-`1` shift-preimage of `curlWitnessSite` -/

/-- **`preWitnessSite1 := (1,3,0)`** — `curlWitnessSite = (1,0,0)` with coordinate `1` set to `3`
(the unique predecessor of `curlWitnessSite` under a direction-`1` shift, mod the periodic extent
`4`). -/
noncomputable def preWitnessSite1 : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  Function.update CoarseCurl.curlWitnessSite 1 3

/-- **`shift_1(preWitnessSite1) = curlWitnessSite`** — kernel-checked (`decide`), all data
concrete/computable. -/
theorem preWitnessSite1_shift :
    periodicLatticeShift preWitnessSite1 1 = CoarseCurl.curlWitnessSite := by
  decide

#print axioms preWitnessSite1_shift

/-! ## §4. The general block-average value formula for `Q_k v` -/

/-- **`(Q_ell v)(y,μ) = (1/16)·[𝟙(pre∈block(y,ell)) − 𝟙(curlWitnessSite∈block(y,ell))]`**, for ANY
coarse base site `y` (with its coarse-lattice membership witness `hy`) and direction `μ`, given the
`μ`-shift-preimage `pre` of `curlWitnessSite`. The `1/16` is `1/(witnessEll:ℝ)^4` evaluated
concretely (`witnessEll = 2`). -/
theorem coarseRestrict_gradWitness_eq (y : PeriodicLatticeSite AdmissibleSubspace.witnessL)
    (hy : y ∈ AdmissibleSubspace.CoarseLattice AdmissibleSubspace.witnessL
      AdmissibleSubspace.witnessEll)
    (μ : Fin 3) (pre : PeriodicLatticeSite AdmissibleSubspace.witnessL)
    (hpre : periodicLatticeShift pre μ = CoarseCurl.curlWitnessSite) :
    coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig (⟨y, hy⟩, μ) =
      (1 / 16 : ℝ) *
        ((if pre ∈ AdmissibleSubspace.blockOf y AdmissibleSubspace.witnessEll then (1 : ℝ) else 0)
          - (if CoarseCurl.curlWitnessSite ∈
              AdmissibleSubspace.blockOf y AdmissibleSubspace.witnessEll then (1 : ℝ) else 0)) := by
  unfold coarseRestrict gradWitnessConfig gradValue
  have hcoef : (1 / (AdmissibleSubspace.witnessEll : ℝ) ^ 4) = 1 / 16 := by
    unfold AdmissibleSubspace.witnessEll; norm_num
  rw [hcoef]
  congr 1
  rw [Finset.sum_sub_distrib,
    sum_gradWitnessLam_shift (AdmissibleSubspace.blockOf y AdmissibleSubspace.witnessEll) μ pre
      hpre,
    sum_gradWitnessLam_plain (AdmissibleSubspace.blockOf y AdmissibleSubspace.witnessEll)]

#print axioms coarseRestrict_gradWitness_eq

/-! ## §5. THE COMPUTATION: `∂₁(Q_kv)` at the witness plaquette equals `1/16 ≠ 0` -/

/-- **`(Q_kv)(witnessY,0) = 0`.** `pre = witnessY` for `μ=0` (`hpre` is `rfl`, since
`curlWitnessSite := periodicLatticeShift witnessY 0` by definition, `CoarseCurl.lean`). Both
membership tests agree (`witnessY` and `curlWitnessSite` are both in `blockOf witnessY witnessEll`),
so the difference vanishes. -/
theorem coarseRestrict_gradWitness_term1 :
    coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (0 : Fin 3)) = 0 := by
  rw [coarseRestrict_gradWitness_eq AdmissibleSubspace.witnessY AdmissibleSubspace.witnessY_coarse
    0 AdmissibleSubspace.witnessY rfl]
  norm_num [show AdmissibleSubspace.witnessY ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll from
    by decide,
    show CoarseCurl.curlWitnessSite ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll from
    by decide]

/-- **`(Q_kv)(coarseShift_0(witnessY),1) = 0`.** Neither `preWitnessSite1` nor `curlWitnessSite`
lies in the shifted block `blockOf (coarseShift witnessY witnessEll 0) witnessEll` (coordinate `0`
of both is `1`, outside `[2,4)`). -/
theorem coarseRestrict_gradWitness_term2 :
    coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 0⟩,
          (1 : Fin 3)) = 0 := by
  rw [coarseRestrict_gradWitness_eq
    (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0)
    (coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 0) 1
    preWitnessSite1 preWitnessSite1_shift]
  norm_num [show preWitnessSite1 ∉
      AdmissibleSubspace.blockOf
        (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0)
        AdmissibleSubspace.witnessEll from by decide,
    show CoarseCurl.curlWitnessSite ∉
      AdmissibleSubspace.blockOf
        (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0)
        AdmissibleSubspace.witnessEll from by decide]

/-- **`(Q_kv)(coarseShift_1(witnessY),0) = 0`.** Neither `witnessY` nor `curlWitnessSite` lies in
the shifted block `blockOf (coarseShift witnessY witnessEll 1) witnessEll` (coordinate `1` of both
is `0`, outside `[2,4)`). -/
theorem coarseRestrict_gradWitness_term3 :
    coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 1⟩,
          (0 : Fin 3)) = 0 := by
  rw [coarseRestrict_gradWitness_eq
    (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1)
    (coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 1) 0
    AdmissibleSubspace.witnessY rfl]
  norm_num [show AdmissibleSubspace.witnessY ∉
      AdmissibleSubspace.blockOf
        (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1)
        AdmissibleSubspace.witnessEll from by decide,
    show CoarseCurl.curlWitnessSite ∉
      AdmissibleSubspace.blockOf
        (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1)
        AdmissibleSubspace.witnessEll from by decide]

/-- **`(Q_kv)(witnessY,1) = -1/16`.** `preWitnessSite1 = (1,3,0) ∉ blockOf witnessY witnessEll`
(coordinate `1` is `3`), but `curlWitnessSite = (1,0,0) ∈ blockOf witnessY witnessEll`, so the
difference is `0 − 1 = −1`, giving `−1/16` — THE ASYMMETRIC TERM that breaks the naive commuting
square: exactly one of the pure-gauge witness's two nonzero contributors per direction survives
into this particular block. -/
theorem coarseRestrict_gradWitness_term4 :
    coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (1 : Fin 3))
      = -1 / 16 := by
  rw [coarseRestrict_gradWitness_eq AdmissibleSubspace.witnessY AdmissibleSubspace.witnessY_coarse
    1 preWitnessSite1 preWitnessSite1_shift]
  norm_num [show preWitnessSite1 ∉
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll from
    by decide,
    show CoarseCurl.curlWitnessSite ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll from
    by decide]

#print axioms coarseRestrict_gradWitness_term1
#print axioms coarseRestrict_gradWitness_term2
#print axioms coarseRestrict_gradWitness_term3
#print axioms coarseRestrict_gradWitness_term4

/-- **THE COMPUTATION: `∂₁(Q_kv)` at the witness plaquette `(witnessY,⟨0,1⟩)` equals `1/16 ≠ 0`.**
Assembled from the four block-average terms above via `coarseCurlValue`'s defining four-term
formula (mirroring `CoarseCurl.lean` §6's exact assembly pattern, LAW-19). -/
theorem coarseCurl_of_coarseRestrict_gradWitness_value :
    coarseCurlValue witnessHdvd (coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs)
      = 1 / 16 := by
  simp only [coarseCurlValue, coarseWitnessDirs]
  change coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (0 : Fin 3))
      + coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 0⟩,
          (1 : Fin 3))
      - coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 1⟩,
          (0 : Fin 3))
      - coarseRestrict AdmissibleSubspace.witnessEll gradWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (1 : Fin 3))
      = 1 / 16
  rw [coarseRestrict_gradWitness_term1, coarseRestrict_gradWitness_term2,
      coarseRestrict_gradWitness_term3, coarseRestrict_gradWitness_term4]
  ring

#print axioms coarseCurl_of_coarseRestrict_gradWitness_value

/-! ## §6. THE VALUE-LEVEL IMPOSSIBILITY THEOREM -/

/-- **NO linear map `M` between the raw plaquette-indexed function spaces can satisfy the
commuting square `∂₁∘Q_k = M∘∂`.** Proof: apply the hypothesis to the pure-gauge witness `v`;
`∂v=0` (general, §1) forces `M(∂v) = M(0) = 0` (linearity), but the LHS `∂₁(Q_kv)` evaluates to
`1/16 ≠ 0` at the witness plaquette (§5) — contradiction. This is the STRONGEST possible negative
answer to the dispatch's question: not merely that the natural averaging candidate fails, but that
NO candidate, of any kind, can work. -/
theorem no_commuting_square_valueLevel
    (M : (PeriodicLatticePlaquette AdmissibleSubspace.witnessL → ℝ) →ₗ[ℝ]
      (CoarseCurl.CoarsePlaquette AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll → ℝ))
    (hM : ∀ A : Bond AdmissibleSubspace.witnessL → ℝ,
      coarseCurlValue witnessHdvd (coarseRestrict AdmissibleSubspace.witnessEll A) =
        M (curlValue A)) :
    False := by
  have h1 : curlValue gradWitnessConfig = 0 := funext gradWitnessConfig_curl_eq_zero
  have h2 := hM gradWitnessConfig
  rw [h1, map_zero] at h2
  have h3 := congrFun h2
    (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs)
  rw [coarseCurl_of_coarseRestrict_gradWitness_value] at h3
  simp only [Pi.zero_apply] at h3
  norm_num at h3

#print axioms no_commuting_square_valueLevel

/-! ## §7. THE OPERATOR-LEVEL (Hilbert-space) COROLLARY -/

/-- **NO `ContinuousLinearMap M : PlaquetteSpace L →L[ℝ] CoarsePlaquetteSpace L ell` satisfies the
exact commuting square `(coarseCurlCLM).comp(coarseRestrictCLM) = M∘curlCLM`** — the direct,
Hilbert-space-level answer to the dispatch's question. Since no such `M` exists AT ALL, the
question "is `M` a manifest contraction with `‖M‖≤1`" is moot: the premise it would act on is
false. Built by transporting the value-level impossibility (§6) through the `_apply` rfl-lemmas
that already relate every `ContinuousLinearMap` in this tree to its underlying raw-function
computation (`gradCLM_apply`, `curlCLM_apply`, `coarseRestrictCLM_apply`, `coarseCurlCLM_apply`,
LAW-19 reuse, no new transport machinery invented). -/
theorem no_commuting_square_operator
    (M : PlaquetteSpace AdmissibleSubspace.witnessL →L[ℝ]
      CoarseCurl.CoarsePlaquetteSpace AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll)
    (hM : ∀ A : BondSpace AdmissibleSubspace.witnessL,
      CoarseCurl.coarseCurlCLM AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll
          witnessHdvd (coarseRestrictCLM AdmissibleSubspace.witnessL
            AdmissibleSubspace.witnessEll A) =
        M (curlCLM AdmissibleSubspace.witnessL A)) :
    False := by
  set lam0 : SiteSpace AdmissibleSubspace.witnessL :=
    (siteEquiv AdmissibleSubspace.witnessL).symm gradWitnessLam with hlam0_def
  set v : BondSpace AdmissibleSubspace.witnessL := gradCLM AdmissibleSubspace.witnessL lam0
    with hv_def
  have hcurlv : curlCLM AdmissibleSubspace.witnessL v = 0 := by
    have hz : (curlCLM AdmissibleSubspace.witnessL).comp (gradCLM AdmissibleSubspace.witnessL)
        lam0 = (0 : SiteSpace AdmissibleSubspace.witnessL →L[ℝ]
          PlaquetteSpace AdmissibleSubspace.witnessL) lam0 := by
      rw [curlCLM_comp_gradCLM_eq_zero]
    simpa [hv_def] using hz
  have heq := hM v
  rw [hcurlv, map_zero] at heq
  have hbv : bondEquiv AdmissibleSubspace.witnessL v = gradWitnessConfig := by
    rw [hv_def, gradCLM_apply, hlam0_def, LinearEquiv.apply_symm_apply]
    rfl
  have hval : CoarseCurl.coarsePlaquetteEquiv AdmissibleSubspace.witnessL
      AdmissibleSubspace.witnessEll
      (CoarseCurl.coarseCurlCLM AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll
        witnessHdvd
        (coarseRestrictCLM AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll v))
      (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs)
      = 1 / 16 := by
    rw [CoarseCurl.coarseCurlCLM_apply, coarseRestrictCLM_apply, hbv]
    exact coarseCurl_of_coarseRestrict_gradWitness_value
  rw [heq, map_zero] at hval
  simp only [Pi.zero_apply] at hval
  norm_num at hval

#print axioms no_commuting_square_operator

/-! ## Remarks connecting §6/§7 to `GOAL_LEMMA.md` Piece 1

The elementary commuting-square route to `⟨B,Δ_kB⟩ ≥ γ₀‖∂₁B‖²` (`γ₀=1`, `k`-uniform, no Fourier)
described in the dispatch is IMPOSSIBLE as a universal operator identity (§6-§7). Combined with
`CoarseCurl.lean`'s prior refutation of the one natural candidate, and the source's own proof of
(1.67) going through the full momentum-space computation (1.60)-(1.66), the three independent
pieces of evidence agree: **Fourier (or an equally deep replacement) is unavoidable for Piece 1**.
Lane A's `CoarseShiftCovariance.lean` remains the live positive route (momentum-diagonalization),
with its own four named residuals (`compute/lane_A_u1momentum/BUILD.md`) — this module does not
change that assessment, it forecloses the one elementary alternative the dispatch asked to test.
-/

end AdalyFormal.Balaban.U1CommutingSquare
