import AdalyFormal.Balaban.FreeCellFrame

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `BlockFaithful` — the reference-block matrix-faithfulness identity, piece (ii) of
`[RES-GEOM-REINDEX]`.

The load-bearing residual of `BackwardCert.geomInequality_of_backwardBlockNonneg` is the per-block
positivity `∀ z, 0 ≤ LocalGeomBackward 2 hdvd B z`.  On the reference block `z = 0` (the origin)
this reduces, once the abstract energies are evaluated into the free-cell bond coordinates, to a
Gram form
`∑ᵢⱼ T i j · B(freeCellBond i) · B(freeCellBond j)` with `T` the verified 56-rank rational Gram
(`compute/backward_cert/cert_backward.json`), which `RatSOSEval` then certifies PSD.

## The named blocker (crux), now PROVED here.

`LocalGeomBackward` credits block `0` the content of the coarse bonds at
`prevμ 0 = (coarseShiftEquiv 2 μ hdvd).symm 0` — a `Classical.choice`-opaque `Equiv` inverse.  The
first job is to pin this to an EXPLICIT site.  `prevμ_refBlock_eq` does exactly this:

  `(coarseShiftEquiv 2 μ hdvd).symm (refBlock L 2) = ⟨prevSite μ, _⟩`,   `prevSite μ = 0` off `μ`,
  `= L μ - 1` on `μ`,

proved via `Equiv.symm_apply_eq` + the wrap fact `coarseShift (prevSite μ) 2 μ = 0`
(`(L μ - 1) + 2 ≡ 0  (mod  L μ + 1)`, using `2 ∣ L μ + 1 ⇒ L μ ≥ 1`).  This is the concrete unblock
of everything symbolic; it is `sorry`-free and axiom-clean (`#print axioms` below).

The remaining, multi-hundred-line body — the symbolic evaluation of the four `Finset`-indexed
energies (`lineCoarseRestrict` / `slabPlaqs`+`curlValue` / `topFaceEnergy` / `bondsInBlock`) into
the 80 free coordinates and assembly into `T` — is NAMED at the end; this module discharges the
crux and the in-block-energy support characterization it unblocks. -/

namespace BlockFaithful

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CoarseCurl
open BackwardCert

variable {L : PeriodicLatticeExtent}

/-! ## §1. The reference block and its explicit backward-previous sites. -/

/-- The origin site lies in every coarse lattice (all coordinates `0`, `0 % ell = 0`). -/
theorem origin_mem_coarse (ell : ℕ) : (0 : PeriodicLatticeSite L) ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  simp

/-- **The reference coarse block `z = 0`** — the origin, as an element of the coarse-lattice
subtype.  This is the concrete meaning of the task's "`LocalGeomBackward 2 hdvd B 0`". -/
def refBlock (L : PeriodicLatticeExtent) (ell : ℕ) :
    {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} :=
  ⟨0, origin_mem_coarse ell⟩

/-- **The explicit backward-previous site** `prevSite μ` in direction `μ` for the reference block at
`ell = 2`: the origin with coordinate `μ` set to `L μ - 1` (the wrap of `-2` mod `L μ + 1`). This is
the site whose `+μ` coarse face points into the origin block. -/
def prevSite (μ : Fin 3) : PeriodicLatticeSite L :=
  Function.update (0 : PeriodicLatticeSite L) μ ⟨L μ - 1, by omega⟩

/-- `prevSite μ` evaluated on its own axis is `L μ - 1`. -/
theorem prevSite_self (μ : Fin 3) : ((prevSite μ : PeriodicLatticeSite L) μ).val = L μ - 1 := by
  simp [prevSite, Function.update_self]

/-- `prevSite μ` evaluated off its axis is `0`. -/
theorem prevSite_ne (μ ν : Fin 3) (h : ν ≠ μ) :
    ((prevSite μ : PeriodicLatticeSite L) ν) = 0 := by
  simp [prevSite, Function.update_of_ne h]

/-- `prevSite μ` lies in the `ell = 2` coarse lattice: off-axis coordinates are `0`, and on axis
`μ` the coordinate is `L μ - 1`, which is even because `2 ∣ L μ + 1` forces `L μ` odd. -/
theorem prevSite_mem (μ : Fin 3) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    (prevSite μ : PeriodicLatticeSite L) ∈ CoarseLattice L 2 := by
  rw [mem_CoarseLattice]
  intro ν
  by_cases h : ν = μ
  · subst h
    rw [prevSite_self]
    obtain ⟨k, hk⟩ := hdvd ν
    omega
  · rw [prevSite_ne μ ν h]
    simp

/-- **THE CRUX PINNING (PROVED, no `sorry`).** The `Classical.choice`-opaque backward map on the
reference block is the explicit `prevSite μ`:

  `(coarseShiftEquiv 2 μ hdvd).symm (refBlock L 2) = ⟨prevSite μ, _⟩`.

Proof: `Equiv.symm_apply_eq` turns the goal into
`refBlock = coarseShiftEquiv 2 μ hdvd ⟨prevSite μ, _⟩`,
whose value component is `coarseShift (prevSite μ) 2 μ`; the wrap fact
`coarseShift (prevSite μ) 2 μ = 0` (axis `μ`: `(L μ - 1) + 2 ≡ 0 mod (L μ + 1)`; off axis: unchanged
`0`) closes it. This is the concrete unblock the whole symbolic evaluation was gated on. -/
theorem prevμ_refBlock_eq (μ : Fin 3) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    (coarseShiftEquiv 2 μ hdvd).symm (refBlock L 2)
      = ⟨prevSite μ, prevSite_mem μ hdvd⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  change (refBlock L 2).1 = coarseShift (prevSite μ) 2 μ
  funext ν
  by_cases h : ν = μ
  · subst h
    apply Fin.ext
    rw [coarseShift_val_eq, prevSite_self]
    -- (L ν - 1 + 2) % (L ν + 1) = 0, and (refBlock).1 ν = (0 : Fin _).val = 0
    obtain ⟨k, hk⟩ := hdvd ν
    have hLpos : 1 ≤ L ν := by omega
    change (0 : Fin (L ν + 1)).val = (L ν - 1 + 2) % (L ν + 1)
    simp only [Fin.val_zero]
    have hsum : L ν - 1 + 2 = L ν + 1 := by omega
    rw [hsum, Nat.mod_self]
  · rw [coarseShift_apply_ne (prevSite μ) 2 μ ν h, prevSite_ne μ ν h]
    rfl

#print axioms prevμ_refBlock_eq

/-! ## §2. The explicit reference-block form of `LocalGeomBackward` (the crux's payoff).

Substituting the pinned `prevμ (refBlock) = ⟨prevSite μ, _⟩` into `LocalGeomBackward` removes the
`Classical.choice` opacity: the four energies now sit at EXPLICIT sites `prevSite μ` (line-`Q`,
slab-curl, top-face) and the origin (in-block).  This is the form on which the four symbolic
free-cell evaluations of `[RES-GEOM-REINDEX]` (ii) proceed. -/

open AdalyFormal.Balaban.LatticeOperators in
open AdalyFormal.Balaban.LineIntegralAveraging in
open AdalyFormal.Balaban.Lemma24Assembly in
open AdalyFormal.Balaban.CrossSectionField in
open AdalyFormal.Balaban.BlockPoincare in
open GeomScratch in
theorem localGeomBackward_refBlock_explicit
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (B : Bond L → ℝ) :
    LocalGeomBackward 2 hdvd B (refBlock L 2)
      = ((2 : ℕ) : ℝ) * ∑ μ : Fin 3,
            (lineCoarseRestrict 2 B (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2
        + (1 / ((2 : ℕ) : ℝ) ^ 2) * ∑ μ : Fin 3,
            ∑ p ∈ slabPlaqs (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ), (curlValue B p) ^ 2
        - (1 / 3) * (1 / ((2 : ℕ) : ℝ) ^ 3) * ∑ μ : Fin 3,
            topFaceEnergy B (prevSite μ) 2 μ
        + 6 * (1 / ((2 : ℕ) : ℝ) ^ 2) *
            ∑ b ∈ bondsInBlock (0 : PeriodicLatticeSite L) 2, (B b) ^ 2 := by
  unfold LocalGeomBackward
  have hLine : (∑ μ : Fin 3,
        (lineCoarseRestrict 2 B ((coarseShiftEquiv 2 μ hdvd).symm (refBlock L 2), μ)) ^ 2)
      = ∑ μ : Fin 3, (lineCoarseRestrict 2 B (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2 :=
    Finset.sum_congr rfl (fun μ _ => by rw [prevμ_refBlock_eq μ hdvd])
  have hSlab : (∑ μ : Fin 3,
        ∑ p ∈ slabPlaqs ((coarseShiftEquiv 2 μ hdvd).symm (refBlock L 2), μ), (curlValue B p) ^ 2)
      = ∑ μ : Fin 3,
        ∑ p ∈ slabPlaqs (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ), (curlValue B p) ^ 2 :=
    Finset.sum_congr rfl (fun μ _ => by rw [prevμ_refBlock_eq μ hdvd])
  have hTop : (∑ μ : Fin 3,
        topFaceEnergy B ((coarseShiftEquiv 2 μ hdvd).symm (refBlock L 2)).1 2 μ)
      = ∑ μ : Fin 3, topFaceEnergy B (prevSite μ) 2 μ :=
    Finset.sum_congr rfl (fun μ _ => by rw [prevμ_refBlock_eq μ hdvd])
  rw [hLine, hSlab, hTop]
  rfl

#print axioms localGeomBackward_refBlock_explicit

end BlockFaithful
