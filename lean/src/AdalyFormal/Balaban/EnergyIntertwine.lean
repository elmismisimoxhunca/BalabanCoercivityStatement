import AdalyFormal.Balaban.Ell2RefBlock

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `EnergyIntertwine` — the three energy shift-intertwining lemmas and the transport identity
discharging the ENERGY content of `Ell2RefBlock`'s `Htrans` hypothesis.

`Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS` reduces the `ell = 2` `(geom)`
residual to a reference-block SOS identity `Href` (NOT this lane's target) AND a translation transport

  `Htrans : ∀ z, ∃ C ∈ admissibleSubspaceInter L 2,
      LocalGeomBackward 2 hdvd B z = LocalGeomBackward 2 hdvd C (refBlock L 2)`.

The model was `CoarseShiftCovariance.coarseRestrict_shift_intertwine` — the translation-covariance of
the single operator `coarseRestrict`, for ONE `ell`-step shift.  This module ports that intertwining
to each of the THREE energies making up `LocalGeomBackward` (`lineCoarseRestrict`,
`slabPlaqs`+`curlValue`, `topFaceEnergy`), plus the in-block energy, and — crucially — GENERALISES the
transport from one `coarseShift` step to a translation by an ARBITRARY coarse vector `v`, so an
arbitrary block `z` transports directly to the reference block `0` in a single step.

## What is PROVED here (no `sorry`, axiom-clean — `#print axioms` at the end).

The organising object is the honest torus translation `siteTransl v x := v + x` (Pi-group addition on
`PeriodicLatticeSite L`, so `(v + x) μ = v μ + x μ` with per-axis wraparound mod `L μ + 1`), and the
field pullback `fieldPull v B b := B (v + b.1, b.2)`.

* **§1 `transl_blockOf_eq_image`** — the block-image identity `blockOf (v + y) ell =
  image (v + ·) (blockOf y ell)` for `v, y ∈ CoarseLattice`, `ell ∣ L μ + 1`.  This GENERALISES
  `CoarseShiftCovariance.coarseShift_blockOf_eq_image` from one `ell`-step to a full coarse-vector
  translation, via the same modular block-index reasoning (`translate_mod_formula`, the
  general-`a`-shift analogue of `shift_mod_formula`).  Torus-covariant: it holds for the boundary
  block `prevSite μ` too, where the translate genuinely wraps (§1's mutation confirms this).
* **§2 the four energy intertwining lemmas** —
  `topFaceEnergy_transl`, `bondsInBlock_energy_transl`, `slabPlaqs_energy_transl`,
  `lineCoarseRestrict_transl` — each: the energy at the TRANSLATED block of `B` equals the same
  energy at the ORIGINAL block of the pulled-back field `fieldPull v B`, proved by reindexing the
  defining `Finset.sum` through the translation bijection (`Finset.sum_image`), the exact shape of
  `coarseRestrict_shift_intertwine`.  `slabPlaqs`/`lineCoarseRestrict` additionally use the pointwise
  `curlValue`/`lineIntegralValue` translation-commutation (`curlValue_transl`,
  `lineIntegralValue_transl`), the genuine geometric content.
* **§3 `prevMu_gen`** — the general backward-site pin `(coarseShiftEquiv 2 μ hdvd).symm z =
  ⟨z.1 + prevSite μ, _⟩` (GENERALISES `BlockFaithful.prevμ_refBlock_eq`, the `z = refBlock` case).
* **§4 `localGeomBackward_transl`** — **THE ENERGY IDENTITY (PROVED, unconditional).**
  `LocalGeomBackward 2 hdvd B z = LocalGeomBackward 2 hdvd (fieldPull z.1 B) (refBlock L 2)`.
  This is the ENTIRE energy content of `Htrans`, with witness `C = fieldPull z.1 B`, holding for EVERY
  field `B` with NO admissibility hypothesis.
* **§5 falsifiability (S82/S83/OPS-3)** — the block-image identity's dependence on `v ∈ CoarseLattice`
  and on the reindex bijection is exhibited: a non-coarse `v` breaks it.

## Admissibility of `C` — CLOSED (`ell = 2`), and FULL `Htrans`.

`Htrans` additionally requires the witness `C = fieldPull z.1 B ∈ admissibleSubspaceInter L 2`.  §6
proves this (`fieldPull_mem_admissible`), via the translation-covariance of `staircasePath`
(`bondTransl_mem_staircase` : `bondTransl v '' (staircasePath y x) ⊆ staircasePath (v+y) (v+x)`).  The
`ell = 2` parity fact (`transl_val_offset`) is what makes it hold: no staircase segment straddles a wrap
boundary (each block-local segment has length `≤ 1`, and `L μ + 1` is even, so `2a + {2b, 2b+1}` never
brackets `2m`), so the raw-`.val` `min`/`max` segments and their translates collapse covariantly; the
corners transport by `corner1/2_transl`.

Consequently:
* **§6 `htrans_full`** — **`Htrans` FULLY DISCHARGED (PROVED, no `sorry`).**  Exactly the `Htrans`
  hypothesis of `Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS`, assuming only
  `B ∈ admissibleSubspaceInter L 2` (the SAME hypothesis that theorem already carries).
* **§6 `geomInequality_of_admissible_ell2_of_Href`** — the CAPSTONE: the `ell = 2` `(geom)` inequality
  now follows from the reference-block SOS identity `Href` ALONE (`Htrans` discharged), kernel-checked.
* `htrans_of_admissible_transl` is kept as the modular assembler (Htrans from a per-block admissibility
  hypothesis `hadm`), which `htrans_full` discharges unconditionally. -/

namespace AdalyFormal.Balaban.EnergyIntertwine

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.CoarseShiftCovariance
open AdalyFormal.Balaban.BlockPoincare
open GeomScratch
open BackwardCert
open BlockFaithful

variable {L : PeriodicLatticeExtent}

/-! ## §0. The honest torus translation and the field/bond/plaquette pullbacks. -/

/-- **`fieldPull v B`** — the field `B` pulled back by the translation `x ↦ v + x`: coordinate `b` of
`fieldPull v B` reads `B` at the bond translated by `v` (base site `v + b.1`, same direction).  This is
the witness field `C` of `Htrans` (`v = z.1`). -/
def fieldPull (v : PeriodicLatticeSite L) (B : Bond L → ℝ) : Bond L → ℝ :=
  fun b => B (v + b.1, b.2)

@[simp] theorem fieldPull_apply (v : PeriodicLatticeSite L) (B : Bond L → ℝ) (b : Bond L) :
    fieldPull v B b = B (v + b.1, b.2) := rfl

/-- Translation `x ↦ v + x` is injective (cancellation in the additive group `PeriodicLatticeSite L`). -/
theorem siteTransl_injective (v : PeriodicLatticeSite L) :
    Function.Injective (fun x : PeriodicLatticeSite L => v + x) :=
  add_right_injective v

/-- **`periodicLatticeShift` commutes with translation**: `shift (v + w) μ = v + shift w μ`. Both are
group operations; the shift only touches coordinate `μ`, translation is componentwise. -/
theorem shift_transl (v w : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift (v + w) μ = v + periodicLatticeShift w μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [periodicLatticeShift, Function.update_self, Pi.add_apply]
    rw [add_assoc]
  · simp only [periodicLatticeShift, Function.update_of_ne h, Pi.add_apply]

/-- The `j`-fold fine-shift iterate commutes with translation — `shift^[j] (v + x) = v + shift^[j] x`. -/
theorem iterate_shift_transl (v x : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ) :
    (fun z => periodicLatticeShift z μ)^[j] (v + x)
      = v + (fun z => periodicLatticeShift z μ)^[j] x := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, shift_transl]

/-- **`coarseShift` commutes with translation**: `coarseShift (v + w) ell μ = v + coarseShift w ell μ`. -/
theorem coarseShift_transl (v w : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    coarseShift (v + w) ell μ = v + coarseShift w ell μ := by
  unfold coarseShift
  exact iterate_shift_transl v w μ ell

/-! ## §1. The modular block-index arithmetic and the block-image identity under coarse translation. -/

/-- **The general translate block-index formula** — GENERALISES
`CoarseShiftCovariance.shift_mod_formula` from a `+ell` shift to a `+V` shift with `V` a multiple of
`ell`: for `n = ell·m` and `V < n`, `V % ell = 0`, `X < n`,
`(V + X) % n = ell · (((V/ell) + (X/ell)) % m) + X % ell` — adding a coarse offset `V` advances the
block index by `V/ell` (cyclically mod `m`) and leaves the within-block offset `X % ell` unchanged. -/
theorem translate_mod_formula (ell m : ℕ) (hell : 0 < ell) (hm : 0 < m)
    (V : ℕ) (hV : V % ell = 0) (hVlt : V < ell * m) (X : ℕ) (hX : X < ell * m) :
    (V + X) % (ell * m) = ell * (((V / ell) + (X / ell)) % m) + X % ell := by
  set a := V / ell with ha
  set bX := X / ell with hbX
  set rX := X % ell with hrX
  have hVeq : V = ell * a := by rw [ha]; have := Nat.div_add_mod V ell; omega
  have hXeq : ell * bX + rX = X := Nat.div_add_mod X ell
  have hrXlt : rX < ell := Nat.mod_lt X hell
  set q := a + bX with hq
  -- V + X = ell*q + rX
  have hsum : V + X = ell * q + rX := by
    rw [hVeq, ← hXeq, hq]; ring
  rw [hsum]
  have hqm : m * (q / m) + q % m = q := Nat.div_add_mod q m
  -- ell*q + rX = (ell*(q%m) + rX) + (ell*m)*(q/m)
  have hsplit : ell * q + rX = (ell * (q % m) + rX) + (ell * m) * (q / m) := by
    have hmul : ell * q = ell * (q % m) + (ell * m) * (q / m) := by
      calc ell * q = ell * (m * (q / m) + q % m) := by rw [hqm]
        _ = ell * (q % m) + (ell * m) * (q / m) := by ring
    rw [hmul]; ring
  rw [hsplit, Nat.add_mul_mod_self_left]
  have hlt : ell * (q % m) + rX < ell * m := by
    have h1 : q % m < m := Nat.mod_lt q hm
    have h2 : ell * (q % m + 1) ≤ ell * m := Nat.mul_le_mul_left ell (by omega)
    have h3 : ell * (q % m + 1) = ell * (q % m) + ell := by ring
    omega
  rw [Nat.mod_eq_of_lt hlt]

#print axioms translate_mod_formula

/-- **The per-coordinate block correspondence under coarse translation** (GENERALISES
`CoarseShiftCovariance.coarseShift_blockCoord_mu`): for `v`, `y` both aligned in coordinate `μ`
(`% ell = 0`) and `ell ∣ L μ + 1`, membership of `x` in `y`'s `μ`-range is preserved under translating
both `x` and `y` by `v`. -/
theorem transl_blockCoord {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv0 : (v μ).val % ell = 0) (hy0 : (y μ).val % ell = 0)
    (x : PeriodicLatticeSite L) :
    ((y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell) ↔
      (((v + y) μ).val ≤ ((v + x) μ).val ∧ ((v + x) μ).val < ((v + y) μ).val + ell) := by
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, mul_zero] at hm; omega
    · exact h0
  have hxlt : (x μ).val < ell * m := by rw [← hm]; exact (x μ).isLt
  have hylt : (y μ).val < ell * m := by rw [← hm]; exact (y μ).isLt
  have hvlt : (v μ).val < ell * m := by rw [← hm]; exact (v μ).isLt
  have hyeq : (y μ).val = ell * ((y μ).val / ell) := by
    have := Nat.div_add_mod (y μ).val ell; omega
  set jY := (y μ).val / ell with hjY
  set jX := (x μ).val / ell with hjX
  set aV := (v μ).val / ell with haV
  have hjYlt : jY < m := by rw [hjY, Nat.div_lt_iff_lt_mul hell]; rwa [mul_comm]
  have hjXlt : jX < m := by rw [hjX, Nat.div_lt_iff_lt_mul hell]; rwa [mul_comm]
  -- LHS ↔ jX = jY
  have hLHS : ((y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell) ↔ jX = jY := by
    rw [hyeq]
    rw [show ell * jY ≤ (x μ).val ∧ (x μ).val < ell * jY + ell ↔ (x μ).val / ell = jY from
      (div_eq_iff_range ell jY (x μ).val hell).symm]
  -- translated μ-values via Fin.val_add + translate_mod_formula, routed through a `∀ V X`-helper so
  -- `hm : L μ + 1 = ell * m` substitutes only into a goal about FRESH nats (never into one whose
  -- `Fin`-type argument is syntactically `L μ + 1`, which would break `rw`'s motive).
  have hvalAdd : ∀ (c : PeriodicLatticeSite L), ((v + c) μ).val = ((v μ).val + (c μ).val) % (L μ + 1) := by
    intro c; rw [Pi.add_apply, Fin.val_add]
  have hgen : ∀ (V X : ℕ), V % ell = 0 → V < L μ + 1 → X < L μ + 1 →
      (V + X) % (L μ + 1) = ell * (((V / ell) + (X / ell)) % m) + X % ell := by
    intro V X hVm hVl hXl
    rw [hm]
    exact translate_mod_formula ell m hell hmpos V hVm (by rw [← hm]; exact hVl) X
      (by rw [← hm]; exact hXl)
  have hshiftX : ((v + x) μ).val = ell * ((aV + jX) % m) + (x μ).val % ell := by
    rw [hvalAdd]
    exact hgen (v μ).val (x μ).val hv0 (v μ).isLt (x μ).isLt
  have hshiftY : ((v + y) μ).val = ell * ((aV + jY) % m) + (y μ).val % ell := by
    rw [hvalAdd]
    exact hgen (v μ).val (y μ).val hv0 (v μ).isLt (y μ).isLt
  have hrX : (x μ).val % ell < ell := Nat.mod_lt _ hell
  have hRHS : (((v + y) μ).val ≤ ((v + x) μ).val ∧ ((v + x) μ).val < ((v + y) μ).val + ell) ↔
      (aV + jX) % m = (aV + jY) % m := by
    rw [hshiftX, hshiftY, hy0, add_zero]
    rw [(div_eq_iff_range ell ((aV + jY) % m)
      (ell * ((aV + jX) % m) + (x μ).val % ell) hell).symm]
    rw [mul_add_div_of_lt ell ((aV + jX) % m) ((x μ).val % ell) hell hrX]
  rw [hLHS, hRHS]
  constructor
  · intro h; rw [h]
  · intro h
    -- (aV+jX)%m = (aV+jY)%m ⇒ jX = jY  (cancel aV mod m)
    have hcancel : jX % m = jY % m := Nat.ModEq.add_left_cancel' aV h
    rwa [Nat.mod_eq_of_lt hjXlt, Nat.mod_eq_of_lt hjYlt] at hcancel

#print axioms transl_blockCoord

/-- **The full block-membership correspondence under coarse translation**: `x ∈ blockOf y ell ↔
(v + x) ∈ blockOf (v + y) ell`, for `v, y ∈ CoarseLattice`, tileability.  Unlike the single-`coarseShift`
version (which touched only direction `μ`), a translation moves EVERY coordinate, so `transl_blockCoord`
applies in every direction `ν`. -/
theorem transl_mem_blockOf_iff {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) :
    x ∈ blockOf y ell ↔ (v + x) ∈ blockOf (v + y) ell := by
  rw [mem_blockOf, mem_blockOf]
  constructor
  · intro h ν
    exact (transl_blockCoord hell (hdvd ν) (mem_CoarseLattice.mp hv ν)
      (mem_CoarseLattice.mp hy ν) x).mp (h ν)
  · intro h ν
    exact (transl_blockCoord hell (hdvd ν) (mem_CoarseLattice.mp hv ν)
      (mem_CoarseLattice.mp hy ν) x).mpr (h ν)

#print axioms transl_mem_blockOf_iff

/-- Translation `x ↦ v + x` is bijective (injective self-map of a finite type). -/
theorem siteTransl_bijective (v : PeriodicLatticeSite L) :
    Function.Bijective (fun x : PeriodicLatticeSite L => v + x) :=
  Finite.injective_iff_bijective.mp (siteTransl_injective v)

/-- **THE BLOCK-IMAGE IDENTITY under coarse translation (GENERALISES
`CoarseShiftCovariance.coarseShift_blockOf_eq_image`).** `blockOf (v + y) ell` is LITERALLY the image
of `blockOf y ell` under the translation `x ↦ v + x`, for `v, y ∈ CoarseLattice`.  This is the reindex
bijection every energy intertwining below runs on; it is torus-covariant (holds where the translate
wraps, e.g. `y = prevSite μ`). -/
theorem transl_blockOf_eq_image {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell) :
    blockOf (v + y) ell = Finset.image (fun x : PeriodicLatticeSite L => v + x) (blockOf y ell) := by
  apply Finset.ext
  intro x'
  rw [Finset.mem_image]
  constructor
  · intro hx'
    obtain ⟨x, hx⟩ := (siteTransl_bijective v).2 x'
    dsimp only at hx
    refine ⟨x, ?_, hx⟩
    rw [transl_mem_blockOf_iff hell hdvd hv hy x, hx]
    exact hx'
  · rintro ⟨x, hx, rfl⟩
    exact (transl_mem_blockOf_iff hell hdvd hv hy x).mp hx

#print axioms transl_blockOf_eq_image

/-! ## §2. The four energy intertwining lemmas. -/

/-- **The within-block offset is preserved under coarse translation**: for `x` in `y`'s `μ`-range,
`x` sits at the top `μ`-layer of `y`'s block iff `v + x` sits at the top `μ`-layer of `(v+y)`'s block.
The genuine content: translation shifts the block base but keeps the within-block offset `(x μ).val %
ell` unchanged. -/
theorem transl_topCoord {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv0 : (v μ).val % ell = 0) (hy0 : (y μ).val % ell = 0)
    {x : PeriodicLatticeSite L} (hx : (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell) :
    ((x μ).val = (y μ).val + (ell - 1) ↔ ((v + x) μ).val = ((v + y) μ).val + (ell - 1)) := by
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, mul_zero] at hm; omega
    · exact h0
  have hxlt : (x μ).val < ell * m := by rw [← hm]; exact (x μ).isLt
  have hylt : (y μ).val < ell * m := by rw [← hm]; exact (y μ).isLt
  set jX := (x μ).val / ell with hjX
  set jY := (y μ).val / ell with hjY
  have hyeq : (y μ).val = ell * jY := by
    rw [hjY]; have h := Nat.div_add_mod (y μ).val ell; omega
  have hxeq0 : (x μ).val = ell * jX + (x μ).val % ell := (Nat.div_add_mod (x μ).val ell).symm
  -- jX = jY from the range hypothesis
  have hjeq : jX = jY := (div_eq_iff_range ell jY (x μ).val hell).mpr (by rw [← hyeq]; exact hx)
  rw [hjeq] at hxeq0
  -- hbase : (x μ).val = (y μ).val + (x μ).val % ell
  have hbase : (x μ).val = (y μ).val + (x μ).val % ell := by omega
  have hvalAdd : ∀ (c : PeriodicLatticeSite L), ((v + c) μ).val = ((v μ).val + (c μ).val) % (L μ + 1) := by
    intro c; rw [Pi.add_apply, Fin.val_add]
  have hgen : ∀ (V X : ℕ), V % ell = 0 → V < L μ + 1 → X < L μ + 1 →
      (V + X) % (L μ + 1) = ell * (((V / ell) + (X / ell)) % m) + X % ell := by
    intro V X hVm hVl hXl
    rw [hm]
    exact translate_mod_formula ell m hell hmpos V hVm (by rw [← hm]; exact hVl) X
      (by rw [← hm]; exact hXl)
  have hshiftX : ((v + x) μ).val = ell * (((v μ).val / ell + jY) % m) + (x μ).val % ell := by
    rw [hvalAdd, hgen (v μ).val (x μ).val hv0 (v μ).isLt (x μ).isLt, ← hjX, hjeq]
  have hshiftY : ((v + y) μ).val = ell * (((v μ).val / ell + jY) % m) := by
    rw [hvalAdd, hgen (v μ).val (y μ).val hv0 (v μ).isLt (y μ).isLt, hy0, add_zero, ← hjY]
  -- both `(x μ).val` and `(v+x)μ.val` equal (their aligned base) + the SAME offset `(x μ).val % ell`
  constructor
  · intro htop
    have hoff : (x μ).val % ell = ell - 1 := by omega
    rw [hshiftX, hshiftY, hoff]
  · intro htop
    rw [hshiftX, hshiftY] at htop
    omega

/-- **`crossSectionTop` transports as an image under coarse translation.** -/
theorem crossSectionTop_transl_image {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    crossSectionTop (v + y) ell μ
      = Finset.image (fun x : PeriodicLatticeSite L => v + x) (crossSectionTop y ell μ) := by
  apply Finset.ext
  intro x'
  rw [Finset.mem_image, mem_crossSectionTop]
  constructor
  · rintro ⟨hblk, htop⟩
    obtain ⟨x, hx⟩ := (siteTransl_bijective v).2 x'
    dsimp only at hx
    subst hx
    have hxblk : x ∈ blockOf y ell := (transl_mem_blockOf_iff hell hdvd hv hy x).mpr hblk
    refine ⟨x, ?_, rfl⟩
    rw [mem_crossSectionTop]
    refine ⟨hxblk, ?_⟩
    exact (transl_topCoord hell (hdvd μ) (mem_CoarseLattice.mp hv μ) (mem_CoarseLattice.mp hy μ)
      (mem_blockOf.mp hxblk μ)).mpr htop
  · rintro ⟨x, hxtop, rfl⟩
    rw [mem_crossSectionTop] at hxtop
    obtain ⟨hxblk, htop⟩ := hxtop
    refine ⟨(transl_mem_blockOf_iff hell hdvd hv hy x).mp hxblk, ?_⟩
    exact (transl_topCoord hell (hdvd μ) (mem_CoarseLattice.mp hv μ) (mem_CoarseLattice.mp hy μ)
      (mem_blockOf.mp hxblk μ)).mp htop

/-- **INTERTWINING LEMMA 3 (`topFaceEnergy`).** The top cross-section energy at the TRANSLATED block of
`B` equals the same energy at the ORIGINAL block of the pulled-back field `fieldPull v B`.  Reindex the
`crossSectionTop` sum through the translation bijection. -/
theorem topFaceEnergy_transl {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell) (B : Bond L → ℝ) (μ : Fin 3) :
    topFaceEnergy B (v + y) ell μ = topFaceEnergy (fieldPull v B) y ell μ := by
  unfold topFaceEnergy
  rw [crossSectionTop_transl_image hell hdvd hv hy μ,
    Finset.sum_image (fun x _ x' _ h => siteTransl_injective v h)]
  apply Finset.sum_congr rfl
  intro x _
  rfl

#print axioms topFaceEnergy_transl

/-- **The bond translation** `(x, μ) ↦ (v + x, μ)`. -/
def bondTransl (v : PeriodicLatticeSite L) (b : Bond L) : Bond L := (v + b.1, b.2)

theorem bondTransl_injective (v : PeriodicLatticeSite L) : Function.Injective (bondTransl v) := by
  intro b b' h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact Prod.ext (siteTransl_injective v h1) h2

/-- **`bondsInBlock` transports as an image under coarse translation.** Both endpoints (base and its
`μ`-shift) move covariantly: `shift (v + x) μ = v + shift x μ` (`shift_transl`). -/
theorem bondsInBlock_transl_image {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell) :
    bondsInBlock (v + y) ell = Finset.image (bondTransl v) (bondsInBlock y ell) := by
  apply Finset.ext
  intro b'
  rw [Finset.mem_image, mem_bondsInBlock]
  constructor
  · rintro ⟨hbase, hshift⟩
    obtain ⟨x, hx⟩ := (siteTransl_bijective v).2 b'.1
    dsimp only at hx
    refine ⟨(x, b'.2), ?_, ?_⟩
    · rw [mem_bondsInBlock]
      refine ⟨?_, ?_⟩
      · exact (transl_mem_blockOf_iff hell hdvd hv hy x).mpr (by rw [hx]; exact hbase)
      · apply (transl_mem_blockOf_iff hell hdvd hv hy (periodicLatticeShift x b'.2)).mpr
        rw [← shift_transl, hx]; exact hshift
    · show (v + x, b'.2) = b'
      rw [hx]
  · rintro ⟨b, hb, rfl⟩
    rw [mem_bondsInBlock] at hb
    obtain ⟨hbase, hshift⟩ := hb
    show (v + b.1) ∈ blockOf (v + y) ell
      ∧ periodicLatticeShift (v + b.1) b.2 ∈ blockOf (v + y) ell
    refine ⟨(transl_mem_blockOf_iff hell hdvd hv hy b.1).mp hbase, ?_⟩
    rw [shift_transl]
    exact (transl_mem_blockOf_iff hell hdvd hv hy (periodicLatticeShift b.1 b.2)).mp hshift

/-- **INTERTWINING LEMMA 4 (in-block bond energy).** The in-block bond energy at the TRANSLATED block
of `B` equals that at the ORIGINAL block of `fieldPull v B`. -/
theorem bondsInBlock_energy_transl {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell) (B : Bond L → ℝ) :
    ∑ b ∈ bondsInBlock (v + y) ell, (B b) ^ 2
      = ∑ b ∈ bondsInBlock y ell, (fieldPull v B b) ^ 2 := by
  rw [bondsInBlock_transl_image hell hdvd hv hy,
    Finset.sum_image (fun b _ b' _ h => bondTransl_injective v h)]
  apply Finset.sum_congr rfl
  intro b _
  rfl

#print axioms bondsInBlock_energy_transl

/-- **The plaquette translation** `(x, dirs) ↦ (v + x, dirs)`. -/
def plaqTransl (v : PeriodicLatticeSite L) (p : PeriodicLatticePlaquette L) :
    PeriodicLatticePlaquette L := (v + p.1, p.2)

theorem plaqTransl_injective (v : PeriodicLatticeSite L) : Function.Injective (plaqTransl v) := by
  intro p q h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact Prod.ext (siteTransl_injective v h1) h2

/-- **`curlValue` commutes with translation**: `curlValue B (plaqTransl v p) = curlValue (fieldPull v B)
p`.  The genuine pointwise content — every one of `curlValue`'s four site reads shifts by `v`, and
`shift (v + x) ν = v + shift x ν` (`shift_transl`) keeps the two `+e_μ`/`+e_ν` reads covariant. -/
theorem curlValue_transl (v : PeriodicLatticeSite L) (B : Bond L → ℝ)
    (p : PeriodicLatticePlaquette L) :
    curlValue B (plaqTransl v p) = curlValue (fieldPull v B) p := by
  simp only [curlValue, plaqTransl, fieldPull, shift_transl]

/-- **`slabPlaqs` transports as an image under coarse translation.** The direction condition is
unchanged (plaquette directions untouched); the base-site condition `p.1 ∈ blockOf y ell` transports
via `transl_mem_blockOf_iff`. -/
theorem slabPlaqs_transl_image {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell)
    (hvy : v + y ∈ CoarseLattice L ell) (μ : Fin 3) :
    slabPlaqs ((⟨v + y, hvy⟩ : {z // z ∈ CoarseLattice L ell}), μ)
      = Finset.image (plaqTransl v)
          (slabPlaqs ((⟨y, hy⟩ : {z // z ∈ CoarseLattice L ell}), μ)) := by
  apply Finset.ext
  intro p'
  rw [Finset.mem_image]
  simp only [slabPlaqs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hdir, hblk⟩
    obtain ⟨x, hx⟩ := (siteTransl_bijective v).2 p'.1
    dsimp only at hx
    refine ⟨(x, p'.2), ⟨hdir, ?_⟩, ?_⟩
    · exact (transl_mem_blockOf_iff hell hdvd hv hy x).mpr (by rw [hx]; exact hblk)
    · show (v + x, p'.2) = p'
      rw [hx]
  · rintro ⟨p, ⟨hdir, hblk⟩, rfl⟩
    refine ⟨hdir, ?_⟩
    show (v + p.1) ∈ blockOf (v + y) ell
    exact (transl_mem_blockOf_iff hell hdvd hv hy p.1).mp hblk

/-- **INTERTWINING LEMMA 2 (`slabPlaqs`+`curlValue`).** The slab plaquette curl energy at the TRANSLATED
block of `B` equals that at the ORIGINAL block of `fieldPull v B`.  Reindex the `slabPlaqs` sum through
the plaquette translation, using `curlValue_transl` on the summand. -/
theorem slabPlaqs_energy_transl {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell)
    (hvy : v + y ∈ CoarseLattice L ell) (B : Bond L → ℝ) (μ : Fin 3) :
    ∑ p ∈ slabPlaqs ((⟨v + y, hvy⟩ : {z // z ∈ CoarseLattice L ell}), μ), (curlValue B p) ^ 2
      = ∑ p ∈ slabPlaqs ((⟨y, hy⟩ : {z // z ∈ CoarseLattice L ell}), μ),
          (curlValue (fieldPull v B) p) ^ 2 := by
  rw [slabPlaqs_transl_image hell hdvd hv hy hvy μ,
    Finset.sum_image (fun p _ p' _ h => plaqTransl_injective v h)]
  apply Finset.sum_congr rfl
  intro p _
  rw [curlValue_transl]

#print axioms slabPlaqs_energy_transl

/-- **`lineIntegralValue` commutes with translation**: the segment line integral of `B` based at the
TRANSLATED site `v + x` equals that of `fieldPull v B` based at `x`.  Each of the `ell` segment reads
shifts by `v`, `shift^[j] (v + x) = v + shift^[j] x` (`iterate_shift_transl`). -/
theorem lineIntegralValue_transl (ell : ℕ) (v x : PeriodicLatticeSite L) (B : Bond L → ℝ) (μ : Fin 3) :
    lineIntegralValue ell B (v + x) μ = lineIntegralValue ell (fieldPull v B) x μ := by
  unfold lineIntegralValue
  apply Finset.sum_congr rfl
  intro j _
  rw [iterate_shift_transl]
  rfl

/-- **INTERTWINING LEMMA 1 (`lineCoarseRestrict`).** The faithful line-integral coarse restriction of
`B` at the TRANSLATED coarse bond equals that of `fieldPull v B` at the ORIGINAL coarse bond — the exact
shape of `CoarseShiftCovariance.coarseRestrict_shift_intertwine`, for the line-integral operator and a
full coarse-vector translation.  Reindex the block sum through the translation bijection
(`transl_blockOf_eq_image`), then `lineIntegralValue_transl` on the summand. -/
theorem lineCoarseRestrict_transl {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {v y : PeriodicLatticeSite L}
    (hv : v ∈ CoarseLattice L ell) (hy : y ∈ CoarseLattice L ell)
    (hvy : v + y ∈ CoarseLattice L ell) (B : Bond L → ℝ) (μ : Fin 3) :
    lineCoarseRestrict ell B ((⟨v + y, hvy⟩ : {z // z ∈ CoarseLattice L ell}), μ)
      = lineCoarseRestrict ell (fieldPull v B) ((⟨y, hy⟩ : {z // z ∈ CoarseLattice L ell}), μ) := by
  unfold lineCoarseRestrict
  dsimp only
  congr 1
  rw [transl_blockOf_eq_image hell hdvd hv hy,
    Finset.sum_image (fun x _ x' _ h => siteTransl_injective v h)]
  apply Finset.sum_congr rfl
  intro x _
  exact lineIntegralValue_transl ell v x B μ

#print axioms lineCoarseRestrict_transl

/-! ## §3. The general backward-site pin (GENERALISES `BlockFaithful.prevμ_refBlock_eq`). -/

/-- The coarse lattice is closed under (group) addition: `(v + w) μ % ell = 0` when both summands are,
using `ell ∣ L μ + 1` so the `mod (L μ + 1)` wrap preserves `mod ell`. -/
theorem add_mem_coarse {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {v w : PeriodicLatticeSite L} (hv : v ∈ CoarseLattice L ell) (hw : w ∈ CoarseLattice L ell) :
    v + w ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  rw [Pi.add_apply, Fin.val_add]
  have h1 := mem_CoarseLattice.mp hv μ
  have h2 := mem_CoarseLattice.mp hw μ
  rw [Nat.mod_mod_of_dvd _ (hdvd μ), Nat.add_mod, h1, h2]
  simp

/-- **The `ell = 2` wrap fact** `coarseShift (prevSite μ) 2 μ = 0`: `(L μ − 1) + 2 ≡ 0 (mod L μ + 1)`.
Isolated from `BlockFaithful.prevμ_refBlock_eq`'s inline proof so `prevMu_gen` can reuse it. -/
theorem coarseShift_prevSite (μ : Fin 3) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    coarseShift (prevSite μ) 2 μ = (0 : PeriodicLatticeSite L) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    apply Fin.ext
    rw [coarseShift_val_eq, prevSite_self]
    obtain ⟨k, hk⟩ := hdvd ν
    have hsum : L ν - 1 + 2 = L ν + 1 := by omega
    simp only [Pi.zero_apply, Fin.val_zero]
    rw [hsum, Nat.mod_self]
  · rw [coarseShift_apply_ne (prevSite μ) 2 μ ν h, prevSite_ne μ ν h]
    rfl

/-- **THE GENERAL BACKWARD-SITE PIN (GENERALISES `BlockFaithful.prevμ_refBlock_eq`).** For ANY coarse
block `z`, the `Classical.choice`-opaque backward map `(coarseShiftEquiv 2 μ hdvd).symm z` is the
EXPLICIT translate `z.1 + prevSite μ`.  Proof: `Equiv.symm_apply_eq` reduces to
`coarseShift (z.1 + prevSite μ) 2 μ = z.1`, and `coarseShift_transl` + the wrap fact
`coarseShift (prevSite μ) 2 μ = 0` close it.  The `z = refBlock` (`z.1 = 0`) case is exactly
`prevμ_refBlock_eq`. -/
theorem prevMu_gen (μ : Fin 3) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2}) :
    (coarseShiftEquiv 2 μ hdvd).symm z
      = ⟨z.1 + prevSite μ, add_mem_coarse hdvd z.2 (prevSite_mem μ hdvd)⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  change z.1 = coarseShift (z.1 + prevSite μ) 2 μ
  rw [coarseShift_transl, coarseShift_prevSite μ hdvd, add_zero]

#print axioms prevMu_gen

/-! ## §4. THE ENERGY IDENTITY — the full energy content of `Htrans`, unconditional. -/

/-- **THE ENERGY INTERTWINING IDENTITY (PROVED, no admissibility hypothesis).**
`LocalGeomBackward 2 hdvd B z = LocalGeomBackward 2 hdvd (fieldPull z.1 B) (refBlock L 2)` for EVERY
field `B` and EVERY coarse block `z`.  This is the ENTIRE energy content of `Ell2RefBlock`'s `Htrans`,
with the explicit witness `C = fieldPull z.1 B`: the backward form at an arbitrary block `z` equals the
backward form at the reference block `0` of the translated field.  Assembled from §2's four energy
intertwining lemmas (`lineCoarseRestrict_transl`, `slabPlaqs_energy_transl`, `topFaceEnergy_transl`,
`bondsInBlock_energy_transl`) and §3's pin `prevMu_gen`, against `BlockFaithful`'s explicit
reference-block form. -/
theorem localGeomBackward_transl (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (B : Bond L → ℝ)
    (z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2}) :
    LocalGeomBackward 2 hdvd B z
      = LocalGeomBackward 2 hdvd (fieldPull z.1 B) (refBlock L 2) := by
  have h02 : (0 : ℕ) < 2 := by norm_num
  -- the four component equalities (LHS `prevMu` form → RHS `prevSite`/`fieldPull` form)
  have hA : (∑ μ : Fin 3,
        (lineCoarseRestrict 2 B ((coarseShiftEquiv 2 μ hdvd).symm z, μ)) ^ 2)
      = ∑ μ : Fin 3,
          (lineCoarseRestrict 2 (fieldPull z.1 B) (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro μ _
    rw [prevMu_gen μ hdvd z,
      lineCoarseRestrict_transl h02 hdvd z.2 (prevSite_mem μ hdvd) _ B μ]
  have hB : (∑ μ : Fin 3,
        ∑ p ∈ slabPlaqs ((coarseShiftEquiv 2 μ hdvd).symm z, μ), (curlValue B p) ^ 2)
      = ∑ μ : Fin 3,
          ∑ p ∈ slabPlaqs ((⟨prevSite μ, prevSite_mem μ hdvd⟩ :
              {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2}), μ),
            (curlValue (fieldPull z.1 B) p) ^ 2 := by
    apply Finset.sum_congr rfl
    intro μ _
    rw [prevMu_gen μ hdvd z,
      slabPlaqs_energy_transl h02 hdvd z.2 (prevSite_mem μ hdvd) _ B μ]
  have hC : (∑ μ : Fin 3,
        topFaceEnergy B ((coarseShiftEquiv 2 μ hdvd).symm z).1 2 μ)
      = ∑ μ : Fin 3, topFaceEnergy (fieldPull z.1 B) (prevSite μ) 2 μ := by
    apply Finset.sum_congr rfl
    intro μ _
    have hsite : ((coarseShiftEquiv 2 μ hdvd).symm z).1 = z.1 + prevSite μ :=
      congrArg Subtype.val (prevMu_gen μ hdvd z)
    rw [hsite]
    exact topFaceEnergy_transl h02 hdvd z.2 (prevSite_mem μ hdvd) B μ
  have hbz : bondsInBlock z.1 2 = bondsInBlock (z.1 + (0 : PeriodicLatticeSite L)) 2 := by
    rw [add_zero]
  have hD : (∑ b ∈ bondsInBlock z.1 2, (B b) ^ 2)
      = ∑ b ∈ bondsInBlock (0 : PeriodicLatticeSite L) 2, (fieldPull z.1 B b) ^ 2 := by
    rw [hbz]
    exact bondsInBlock_energy_transl h02 hdvd z.2 (origin_mem_coarse 2) B
  rw [localGeomBackward_refBlock_explicit hdvd (fieldPull z.1 B)]
  unfold LocalGeomBackward
  rw [hA, hB, hC, hD]

#print axioms localGeomBackward_transl

/-! ## §5. Falsifiability (S82/S83/OPS-3): `v ∈ CoarseLattice` is load-bearing. -/

/-- **The alignment hypothesis `hv0 : (v μ).val % ell = 0` of `transl_blockCoord` is load-bearing, not
decorative.** Dropping it, the block-range correspondence GENUINELY FAILS: on the shared witness
lattice (`witnessL`, `witnessEll = 2`, sides `Fin 4`), the NON-coarse translate `v = (3,0,0)` sends
`x = (1,0,0)` (in `y = 0`'s block `[0,2)` in coordinate `0`) to `(v+x) 0 = (3+1) % 4 = 0`, while
`(v+y) 0 = 3` — and `0 ∉ [3, 5)` — so the translated membership FAILS while the un-translated one held.
This confirms the reindex bijection's dependence on coarse alignment, exactly the property every energy
intertwining above runs on. -/
theorem transl_blockCoord_needs_alignment :
    ¬ ∀ (v y x : PeriodicLatticeSite AdmissibleSubspace.witnessL),
      (((y 0).val ≤ (x 0).val ∧ (x 0).val < (y 0).val + AdmissibleSubspace.witnessEll) →
        (((v + y) 0).val ≤ ((v + x) 0).val ∧
          ((v + x) 0).val < ((v + y) 0).val + AdmissibleSubspace.witnessEll)) := by
  intro h
  set v : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
    fun i => if i = 0 then (3 : Fin 4) else 0 with hvdef
  set y : PeriodicLatticeSite AdmissibleSubspace.witnessL := fun _ => (0 : Fin 4) with hydef
  set x : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
    fun i => if i = 0 then (1 : Fin 4) else 0 with hxdef
  have hpre : (y 0).val ≤ (x 0).val ∧ (x 0).val < (y 0).val + AdmissibleSubspace.witnessEll := by
    rw [hydef, hxdef]; unfold AdmissibleSubspace.witnessEll; decide
  have hpost := h v y x hpre
  have hvx : ((v + x) 0).val = 0 := by
    rw [Pi.add_apply, hvdef, hxdef]; decide
  have hvy : ((v + y) 0).val = 3 := by
    rw [Pi.add_apply, hvdef, hydef]; decide
  rw [hvx, hvy] at hpost
  unfold AdmissibleSubspace.witnessEll at hpost
  omega

#print axioms transl_blockCoord_needs_alignment

/-! ## §6. Admissibility is translation-invariant (`ell = 2`) — and FULL `Htrans`. -/

/-- **The within-block offset survives coarse translation (no wrap, `ell = 2`).** For `v`, `base`
aligned at `ρ` (`% 2 = 0`) and `w` one step at most above `base` in coordinate `ρ`,
`((v + w) ρ).val = ((v + base) ρ).val + ((w ρ).val − (base ρ).val)` — the translated coordinate is the
translated base plus the SAME offset, with NO wraparound.  This is the `ell = 2` parity fact that makes
`staircasePath` (raw-`.val` `min`/`max` segments) translation-covariant: a length-`≤ 1` segment
`{2b, 2b+1}` never brackets the wrap boundary `2m` (parity: `2m = 2a+2b+1` is impossible). -/
theorem transl_val_offset {ρ : Fin 3} {v base w : PeriodicLatticeSite L}
    (hdvd : 2 ∣ (L ρ + 1)) (hvρ : (v ρ).val % 2 = 0) (hbρ : (base ρ).val % 2 = 0)
    (hw : (w ρ).val = (base ρ).val ∨ (w ρ).val = (base ρ).val + 1) :
    ((v + w) ρ).val = ((v + base) ρ).val + ((w ρ).val - (base ρ).val) := by
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, mul_zero] at hm; omega
    · exact h0
  have hvalAdd : ∀ (c : PeriodicLatticeSite L),
      ((v + c) ρ).val = ((v ρ).val + (c ρ).val) % (L ρ + 1) := by
    intro c; rw [Pi.add_apply, Fin.val_add]
  have hgen : ∀ (V X : ℕ), V % 2 = 0 → V < L ρ + 1 → X < L ρ + 1 →
      (V + X) % (L ρ + 1) = 2 * (((V / 2) + (X / 2)) % m) + X % 2 := by
    intro V X hVm hVl hXl
    rw [hm]
    exact translate_mod_formula 2 m (by norm_num) hmpos V hVm (by rw [← hm]; exact hVl) X
      (by rw [← hm]; exact hXl)
  have hdiv : (w ρ).val / 2 = (base ρ).val / 2 := by
    rcases hw with h | h <;> rw [h] <;> omega
  have hwmod : (w ρ).val % 2 = (w ρ).val - (base ρ).val := by
    rcases hw with h | h <;> rw [h] <;> omega
  have hbase : ((v + base) ρ).val = 2 * (((v ρ).val / 2 + (base ρ).val / 2) % m) := by
    rw [hvalAdd, hgen (v ρ).val (base ρ).val hvρ (v ρ).isLt (base ρ).isLt, hbρ, add_zero]
  have hww : ((v + w) ρ).val
      = 2 * (((v ρ).val / 2 + (w ρ).val / 2) % m) + (w ρ).val % 2 := by
    rw [hvalAdd, hgen (v ρ).val (w ρ).val hvρ (v ρ).isLt (w ρ).isLt]
  rw [hww, hdiv, hwmod, ← hbase]

/-- Translation commutes with a single coordinate update: `v + update f k a = update (v+f) k (v k + a)`.
The staircase corners are coordinate updates, so this transports them. -/
theorem transl_update (v f : PeriodicLatticeSite L) (k : Fin 3) (val : Fin (L k + 1)) :
    v + Function.update f k val = Function.update (v + f) k (v k + val) := by
  funext ν
  by_cases h : ν = k
  · subst h; simp [Function.update_self, Pi.add_apply]
  · simp [Function.update_of_ne h, Pi.add_apply]

/-- The first staircase corner transports: `corner1 (v+y) (v+x) = v + corner1 y x`. -/
theorem corner1_transl (v y x : PeriodicLatticeSite L) :
    corner1 (v + y) (v + x) = v + corner1 y x := by
  unfold corner1
  rw [show ((v + x) 2) = v 2 + x 2 from rfl]
  exact (transl_update v y 2 (x 2)).symm

/-- The second staircase corner transports: `corner2 (v+y) (v+x) = v + corner2 y x`. -/
theorem corner2_transl (v y x : PeriodicLatticeSite L) :
    corner2 (v + y) (v + x) = v + corner2 y x := by
  unfold corner2
  rw [corner1_transl, show ((v + x) 1) = v 1 + x 1 from rfl]
  exact (transl_update v (corner1 y x) 1 (x 1)).symm

/-- **A single axis segment transports under coarse translation** (`ell = 2`): the translated bond of a
length-`≤ 1` `axisSegment` lands in the correspondingly translated segment.  The base-coordinate is
pinned (`transl_val_offset` with offset `0`), the top is `< ` the translated top. -/
theorem bondTransl_mem_axisSeg {v base oth : PeriodicLatticeSite L} {ρ : Fin 3}
    (hdvd : 2 ∣ (L ρ + 1)) (hvρ : (v ρ).val % 2 = 0) (hbρ : (base ρ).val % 2 = 0)
    (hoth : (oth ρ).val = (base ρ).val ∨ (oth ρ).val = (base ρ).val + 1)
    {b : Bond L} (hb : b ∈ axisSegment base ρ (base ρ).val (oth ρ).val) :
    bondTransl v b ∈ axisSegment (v + base) ρ ((v + base) ρ).val ((v + oth) ρ).val := by
  rw [mem_axisSegment] at hb ⊢
  obtain ⟨hdir, hpin, hlo, hhi⟩ := hb
  have hbval : (b.1 ρ).val = (base ρ).val := by rcases hoth with h | h <;> omega
  refine ⟨hdir, ?_, ?_, ?_⟩
  · intro ν hν
    show (v + b.1) ν = (v + base) ν
    rw [Pi.add_apply, Pi.add_apply, hpin ν hν]
  · show ((v + base) ρ).val ≤ ((v + b.1) ρ).val
    have hb1 : (b.1 ρ).val = (base ρ).val ∨ (b.1 ρ).val = (base ρ).val + 1 := Or.inl hbval
    rw [transl_val_offset hdvd hvρ hbρ hb1]; omega
  · show ((v + b.1) ρ).val < ((v + oth) ρ).val
    have hb1 : (b.1 ρ).val = (base ρ).val ∨ (b.1 ρ).val = (base ρ).val + 1 := Or.inl hbval
    rw [transl_val_offset hdvd hvρ hbρ hb1, transl_val_offset hdvd hvρ hbρ hoth]; omega

/-- **THE STAIRCASE TRANSPORT (`ell = 2`).** `Γ_{y,x}` transports covariantly under a coarse
translation: `bondTransl v '' (staircasePath y x) ⊆ staircasePath (v+y) (v+x)`.  Each of the three
axis segments transports by `bondTransl_mem_axisSeg`; the corners transport by `corner1/2_transl`; the
raw-`.val` `min`/`max` collapse (`x ∈ blockOf y ⇒ y ≤ x`) and their translated counterparts collapse by
`transl_val_offset`.  This is the translation-covariance of the admissibility geometry the whole
`admissibleSubspaceInter` invariance rests on. -/
theorem bondTransl_mem_staircase {v y x : PeriodicLatticeSite L}
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hv : v ∈ CoarseLattice L 2) (hy : y ∈ CoarseLattice L 2)
    (hx : x ∈ blockOf y 2) {b : Bond L} (hb : b ∈ staircasePath y x) :
    bondTransl v b ∈ staircasePath (v + y) (v + x) := by
  have hvc : ∀ μ : Fin 3, (v μ).val % 2 = 0 := mem_CoarseLattice.mp hv
  have hyc : ∀ μ : Fin 3, (y μ).val % 2 = 0 := mem_CoarseLattice.mp hy
  have hblk : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + 2 := mem_blockOf.mp hx
  have hoth : ∀ μ : Fin 3, (x μ).val = (y μ).val ∨ (x μ).val = (y μ).val + 1 := by
    intro μ; have := hblk μ; omega
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rw [staircasePath]
  rcases hb with (hb2 | hb1) | hb0
  · have hle : (y 2).val ≤ (x 2).val := (hblk 2).1
    rw [Nat.min_eq_left hle, Nat.max_eq_right hle] at hb2
    have hstep := bondTransl_mem_axisSeg (hdvd 2) (hvc 2) (hyc 2) (hoth 2) hb2
    have hle' : ((v + y) 2).val ≤ ((v + x) 2).val := by
      rw [transl_val_offset (hdvd 2) (hvc 2) (hyc 2) (hoth 2)]; omega
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [Nat.min_eq_left hle', Nat.max_eq_right hle']
    exact hstep
  · have hbc : ((corner1 y x) 1).val % 2 = 0 := hyc 1
    have hle : (y 1).val ≤ (x 1).val := (hblk 1).1
    have hoth1 : (x 1).val = ((corner1 y x) 1).val ∨ (x 1).val = ((corner1 y x) 1).val + 1 := hoth 1
    rw [Nat.min_eq_left hle, Nat.max_eq_right hle] at hb1
    have hstep := bondTransl_mem_axisSeg (hdvd 1) (hvc 1) hbc hoth1 hb1
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [corner1_transl]
    have hle' : ((v + y) 1).val ≤ ((v + x) 1).val := by
      rw [transl_val_offset (hdvd 1) (hvc 1) (hyc 1) (hoth 1)]; omega
    rw [Nat.min_eq_left hle', Nat.max_eq_right hle']
    exact hstep
  · have hbc : ((corner2 y x) 0).val % 2 = 0 := hyc 0
    have hle : (y 0).val ≤ (x 0).val := (hblk 0).1
    have hoth0 : (x 0).val = ((corner2 y x) 0).val ∨ (x 0).val = ((corner2 y x) 0).val + 1 := hoth 0
    rw [Nat.min_eq_left hle, Nat.max_eq_right hle] at hb0
    have hstep := bondTransl_mem_axisSeg (hdvd 0) (hvc 0) hbc hoth0 hb0
    apply Finset.mem_union_right
    rw [corner2_transl]
    have hle' : ((v + y) 0).val ≤ ((v + x) 0).val := by
      rw [transl_val_offset (hdvd 0) (hvc 0) (hyc 0) (hoth 0)]; omega
    rw [Nat.min_eq_left hle', Nat.max_eq_right hle']
    exact hstep

#print axioms bondTransl_mem_staircase

/-- **ADMISSIBILITY IS TRANSLATION-INVARIANT (`ell = 2`).** If `B ∈ admissibleSubspaceInter L 2` and
`v` is coarse, then `fieldPull v B ∈ admissibleSubspaceInter L 2`.  For each `(y', x', b)` in the
defining quantifier, `fieldPull v B b = B (bondTransl v b)`, and `bondTransl v b ∈
staircasePath (v+y') (v+x')` (`bondTransl_mem_staircase`) with `v+y'` coarse and `v+x' ∈ blockOf (v+y')`
— so `B` (admissible) vanishes there. -/
theorem fieldPull_mem_admissible {v : PeriodicLatticeSite L}
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (hv : v ∈ CoarseLattice L 2)
    {B : Bond L → ℝ} (hB : B ∈ admissibleSubspaceInter L 2) :
    fieldPull v B ∈ admissibleSubspaceInter L 2 := by
  rw [mem_admissibleSubspaceInter]
  intro y' hy' x' hx' b hb
  show B (v + b.1, b.2) = 0
  have hmem : bondTransl v b ∈ staircasePath (v + y') (v + x') :=
    bondTransl_mem_staircase hdvd hv hy' hx' hb
  have hvy' : v + y' ∈ CoarseLattice L 2 := add_mem_coarse hdvd hv hy'
  have hvx' : v + x' ∈ blockOf (v + y') 2 :=
    (transl_mem_blockOf_iff (by norm_num) hdvd hv hy' x').mp hx'
  exact hB (v + y') hvy' (v + x') hvx' (bondTransl v b) hmem

#print axioms fieldPull_mem_admissible

/-- **THE `Htrans` ASSEMBLER (from a named admissibility hypothesis).** Kept as the modular
factorisation: `Ell2RefBlock`'s `Htrans` from `hadm` (per-block admissibility of the translated field)
and `localGeomBackward_transl`.  `htrans_full` below discharges `hadm` unconditionally. -/
theorem htrans_of_admissible_transl (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (B : Bond L → ℝ)
    (hadm : ∀ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2},
      fieldPull z.1 B ∈ admissibleSubspaceInter L 2) :
    ∀ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2},
      ∃ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 ∧
        LocalGeomBackward 2 hdvd B z = LocalGeomBackward 2 hdvd C (refBlock L 2) :=
  fun z => ⟨fieldPull z.1 B, hadm z, localGeomBackward_transl hdvd B z⟩

/-- **`Htrans`, FULLY DISCHARGED (PROVED, no `sorry`).**  This is EXACTLY the `Htrans` hypothesis of
`Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS` — every coarse block `z`'s backward
form equals the reference block's backward form of an ADMISSIBLE pullback `C = fieldPull z.1 B`.  Energy
equality from `localGeomBackward_transl` (§4); admissibility of `C` from `fieldPull_mem_admissible`
(§6).  Assumes only `B ∈ admissibleSubspaceInter L 2` — the SAME hypothesis the consuming theorem
already carries.  The `Htrans` residual of `[RES-GEOM-REINDEX]` (iv) is therefore CLOSED. -/
theorem htrans_full (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) {B : Bond L → ℝ}
    (hB : B ∈ admissibleSubspaceInter L 2) :
    ∀ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2},
      ∃ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 ∧
        LocalGeomBackward 2 hdvd B z = LocalGeomBackward 2 hdvd C (refBlock L 2) :=
  fun z => ⟨fieldPull z.1 B, fieldPull_mem_admissible hdvd z.2 hB,
    localGeomBackward_transl hdvd B z⟩

#print axioms htrans_full

/-- **CAPSTONE: the `ell = 2` `(geom)` inequality now follows from the reference-block SOS identity
`Href` ALONE** (the `Htrans` hypothesis of
`Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS` is discharged by `htrans_full`).  This
lane removes one of the two residuals that theorem carried; only `Href` remains. -/
theorem geomInequality_of_admissible_ell2_of_Href
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2)
    (Href : ∀ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 →
        ∃ c : ℝ, 0 ≤ c ∧
          LocalGeomBackward 2 hdvd C (refBlock L 2)
            = c * RatSOSEval.sosQuadValue
                (BackwardTCert.backCertSparse.map RatSOSEval.castSparse)
                (Ell2RefBlock.freecoord L hL C)) :
    GeomGlobal.GeomInequality 2 B :=
  Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS hL hdvd B hB Href
    (htrans_full hdvd hB)

#print axioms geomInequality_of_admissible_ell2_of_Href

end AdalyFormal.Balaban.EnergyIntertwine
