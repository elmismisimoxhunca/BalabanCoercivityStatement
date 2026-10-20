/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.OnRangeCoercivity
import AdalyFormal.Balaban.ThirdLevelStokes
import AdalyFormal.Balaban.U1AnchorCoarse
import AdalyFormal.Balaban.StridedAveraging
import AdalyFormal.Balaban.HarmonicModes

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `VRestrictedRoute.lean` — the source's own coarse subspace `V`, and a POSITIVE bound on it

Lane record: `compute/v_route/PROGRESS.md`.

## What this module answers

`OnRangeCoercivity.lean` proved the wall and derived the door:

* the on-range gauge-fixed bound at `V = ⊤` is **FALSE**, and the refuting family is *every* nonzero
  site-constant coarse mode (`onRange_false_by_siteConst`);
* the hypothesis domain the source's own restriction induces is `H₁(V) = G(Q*(S V))`
  (`next_coercive_gf_on_subspace`), and a `V` can rescue the route **only** by excluding that
  family (`subspace_false_of_siteConst`);
* `VzeroAtOrigin_nontrivial` shows such a `V` exists — but §5e states plainly that **no positive
  bound on any nontrivial `H₁(V)` was proved there**.

This module proves one, with the source's own `V`.

## §0 — THE SOURCE SENTENCE, quoted

`corpus/pages/CMP99b_p428.md` (`verification_status: adjudicated`; render
`corpus/renders/CMP99b_p428-40.png`, sha256
`128b1172e7090661d2c2ead70d9514244567c17a43c709ff87b18603b3012d54`), of `(3.156)`:

> This form is considered on the subspace
> `{B : B=0 on Λᶜ, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`.

Three clauses, all on the **coarse** variable `B`. `VSrc` below is exactly these three, in order.

**SCOPE, stated and not hidden — clause (c1) is vacuous on this carrier.** This tree's lattice is
the periodic torus; `Λ` is all of it, so `Λᶜ = ∅` and "`B = 0` on `Λᶜ`" is `True`. It is carried in
`VSrc` as an explicit `True` conjunct rather than dropped, so a reader counting clauses against the
source finds three. Every theorem below is therefore about a subspace that is *larger* than the
source's on a lattice with a genuine `Λ ⊊` boundary: the coercivity results are **not** helped by
the missing clause, and the exclusion result would only get easier with it.

**SCOPE — which `Q₁`.** `(c3)`'s `Q₁` is read here as *the tree's own averaging operator, one level
up*: `lineCoarseRestrictCov (trivialU) 2` at the coarse lattice regarded as a lattice in its own
right (§1). That is the reading which makes the coarse-level statement literally an instance of the
fine-level theorem. `StridedAveraging.qStepCLM 2 U 2` is a second candidate reading; the two are not
proved equal here (that intertwining is not built in this tree). **The exclusion theorem §3 uses
only clause (c2)**, so the hinge of this module does not depend on the adjudication of `Q₁` at all.
Only §4's coarse fibre bound consumes (c3), and it consumes it in exactly the transported form
`VSrc` states.

## §1 — the one object this tree did not have

`DeltaKSuTwoCarrier.lean` records as a measured fact that the reindexing
`CoarseBond L ell → Bond (coarseExtent L ell)` exists in this tree **only for ℝ-valued fields**
(`U1AnchorCoarse.pullback`, the U(1) lane), and that its absence for `SuTwo` blocked a different
construction. §1 builds it, as an `Equiv` on index types plus the induced pullback of `SuTwo`-valued
fields, and transports the two energies and the curl. Declared reusable (LAW-19).

The identification is not an analogy: `U1AnchorCoarse.toFine_shift` already proves the coarse
lattice's own unit shift IS the fine lattice's `coarseShift · ell`.

## §2-§6 — the chain

Write `D = ⟨x, Δ_k(1) x⟩ = curlEnergy x`, `P = ⟨x, P_Ax x⟩ = pAx x`, `Q = qCLM (trivialU L) 2`.

2. `VSrc` (§2): the three clauses.
3. **THE HINGE** (§3): no nonzero site-constant coarse mode is in `VSrc` — by clause (c2) alone.
   `staircasePath_exists_dir_of_ne` puts a direction-`ρ` bond into `Ax(y)` for every direction `ρ`
   whose block is nondegenerate, and a site-constant mode takes the value `g ρ ≠ 0` on every such
   bond. So the §5d wall does not reach `VSrc`. (Had some site-constant mode survived both coarse
   clauses, that would have been a deeper wall; it does not.)
4. **THE COARSE FIBRE BOUND** (§4): `FibreAggregate.aggregate_fibre_bound_gamma` is a theorem at
   EVERY periodic extent. Instantiated at `coarseExtent L 2` on the transported field, with (c3)
   supplying its `Q`-hypothesis and (c2) killing its `pAx` term via
   `AxialCoercivity.pAx_eq_zero_of_vanishing_on_Ax`, it gives
   `γ_agg · ‖B‖² ≤ coarseCurlEnergy B` with `γ_agg = 1/3316224`, `L`-free.
5. **STOKES** (§5): `ThirdLevelStokes.stokes_flat` (`U = 1`, every `ell`, every compatible torus)
   plus Cauchy–Schwarz on its `ell⁵` summands, the block partition
   (`StridedAveraging.coarseLattice_eq_biUnion`) and translation invariance of the plaquette sum
   give `coarseCurlEnergy (Q x) ≤ ell⁻¹ · curlEnergy x`.
6. **THE DESCENT** (§6): with `ExtentUniformCoercivity.defect_bound_at_tree_operators`
   (`γ₀‖x‖² ≤ D + P + C‖Qx‖²`, `γ₀ = 1/13264896`, `C = 13583253568/13264896`) the three combine to
   `γ_V ‖x‖² ≤ D + P` for **every** fine `x` whose coarse datum `Q x` lies in `VSrc` — not merely
   on `H₁(VSrc)`, which is the subset `next_coercive_gf_on_subspace` actually evaluates. Feeding it
   there closes the one-step law on `VSrc`.

`γ_V = γ₀ / (1 + C/(2·γ_agg))`, every factor counted: `C/(2γ_agg) = 13583253568·3316224/(2·13264896)`.
-/

namespace AdalyFormal.Balaban.VRestrictedRoute

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLatticePlaquette PeriodicPlaquetteDirections periodicLatticeShift)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf mem_blockOf
  mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.U1AnchorCoarse (coarseExtent coarseExtent_spec toFine toIdx toFine_val
  toFine_mem toIdx_toFine toFine_toIdx toFine_shift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.AxialContour (Ax mem_Ax)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAx_eq_zero_of_vanishing_on_Ax)

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE `SuTwo` COARSE REINDEXING

`CoarseBond L ell ≃ Bond (coarseExtent L ell)`, and the induced pullback on `SuTwo`-valued fields,
with the two energies and the curl transported. This is `U1AnchorCoarse.pullback`'s `SuTwo`
counterpart — the object `DeltaKSuTwoCarrier.lean` records as absent from this tree. -/

/-- Coarse bond of `L` ↦ bond of the coarse-index lattice. -/
def cbToBond (L : PeriodicLatticeExtent) (ell : ℕ) (c : CoarseBond L ell) :
    Bond (coarseExtent L ell) := (toIdx L ell c.1.1, c.2)

/-- Bond of the coarse-index lattice ↦ coarse bond of `L`. -/
def bondToCb (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (e : Bond (coarseExtent L ell)) : CoarseBond L ell :=
  (⟨toFine L ell e.1, toFine_mem hell hdvd e.1⟩, e.2)

/-- **THE INDEX EQUIVALENCE.** Both directions are `U1AnchorCoarse`'s already-proved site
bijection, tensored with the identity on directions. -/
def cbEquiv (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    CoarseBond L ell ≃ Bond (coarseExtent L ell) where
  toFun := cbToBond L ell
  invFun := bondToCb hell hdvd
  left_inv := by
    rintro ⟨⟨y, hy⟩, μ⟩
    exact Prod.ext (Subtype.ext (toFine_toIdx hell hdvd hy)) rfl
  right_inv := by
    rintro ⟨a, μ⟩
    exact Prod.ext (toIdx_toFine hell hdvd a) rfl

/-- Coarse plaquette ↦ plaquette of the coarse-index lattice. -/
def cpToPlaq (L : PeriodicLatticeExtent) (ell : ℕ) (q : CoarsePlaquette L ell) :
    PeriodicLatticePlaquette (coarseExtent L ell) := (toIdx L ell q.1.1, q.2)

/-- Plaquette of the coarse-index lattice ↦ coarse plaquette. -/
def plaqToCp (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (p : PeriodicLatticePlaquette (coarseExtent L ell)) : CoarsePlaquette L ell :=
  (⟨toFine L ell p.1, toFine_mem hell hdvd p.1⟩, p.2)

/-- The plaquette equivalence, same construction as `cbEquiv`. -/
def cpEquiv (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    CoarsePlaquette L ell ≃ PeriodicLatticePlaquette (coarseExtent L ell) where
  toFun := cpToPlaq L ell
  invFun := plaqToCp hell hdvd
  left_inv := by
    rintro ⟨⟨y, hy⟩, d⟩
    exact Prod.ext (Subtype.ext (toFine_toIdx hell hdvd hy)) rfl
  right_inv := by
    rintro ⟨a, d⟩
    exact Prod.ext (toIdx_toFine hell hdvd a) rfl

/-- **THE PULLBACK OF A `SuTwo`-VALUED COARSE FIELD** to a bond field on the coarse-index lattice.
Same formula as `U1AnchorCoarse.pullback`, codomain `SuTwo` instead of `ℝ`. -/
def pullS (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) : Bond (coarseExtent L ell) → SuTwo :=
  fun e => F (bondToCb hell hdvd e)

theorem pullS_apply (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) (e : Bond (coarseExtent L ell)) :
    pullS hell hdvd F e = F (bondToCb hell hdvd e) := rfl

/-- The pullback is additive and homogeneous — it is a reindexing, so this is definitional. -/
theorem pullS_add (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F G : CoarseBond L ell → SuTwo) :
    pullS hell hdvd (F + G) = pullS hell hdvd F + pullS hell hdvd G := rfl

theorem pullS_smul (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (t : ℝ)
    (F : CoarseBond L ell → SuTwo) :
    pullS hell hdvd (t • F) = t • pullS hell hdvd F := rfl

/-- The `ℓ²` energy of a coarse field, at any scale (`ExtentUniformCoercivity.coarseEnergy` is the
`ell = 2` instance of this). -/
noncomputable def cEnergy (F : CoarseBond L ell → SuTwo) : ℝ := ∑ c : CoarseBond L ell, ‖F c‖ ^ 2

/-- **ENERGY TRANSPORTS.** -/
theorem bondEnergy_pullS (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) : bondEnergy (pullS hell hdvd F) = cEnergy F := by
  unfold bondEnergy cEnergy
  exact Fintype.sum_equiv (cbEquiv hell hdvd).symm _ _ (fun _ => rfl)

/-- **THE CURL TRANSPORTS.** The flat curl of the pulled-back field at a plaquette of the
coarse-index lattice IS the coarse curl of the original field at the corresponding coarse
plaquette. The only input is `toFine_shift`. -/
theorem flatCurl_pullS (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) (p : PeriodicLatticePlaquette (coarseExtent L ell)) :
    flatCurlValue (pullS hell hdvd F) p = coarseCurlSuTwo hdvd F (plaqToCp hell hdvd p) := by
  have e1 : bondToCb hell hdvd (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      = ((⟨coarseShift (toFine L ell p.1) ell p.2.1.1,
          coarseShift_mem_coarseLattice hdvd (toFine_mem hell hdvd p.1) p.2.1.1⟩ :
          {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}), p.2.1.2) :=
    Prod.ext (Subtype.ext (toFine_shift hell hdvd p.1 p.2.1.1)) rfl
  have e2 : bondToCb hell hdvd (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
      = ((⟨coarseShift (toFine L ell p.1) ell p.2.1.2,
          coarseShift_mem_coarseLattice hdvd (toFine_mem hell hdvd p.1) p.2.1.2⟩ :
          {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}), p.2.1.1) :=
    Prod.ext (Subtype.ext (toFine_shift hell hdvd p.1 p.2.1.2)) rfl
  show F _ + F _ - F _ - F _ = F _ + F _ - F _ - F _
  rw [e1, e2]
  rfl

/-- The coarse curl energy, at any scale. -/
noncomputable def coarseCurlEnergy (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ q : CoarsePlaquette L ell, ‖coarseCurlSuTwo hdvd F q‖ ^ 2

theorem coarseCurlEnergy_nonneg (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) : 0 ≤ coarseCurlEnergy hdvd F :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem curlEnergy_pullS (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) :
    curlEnergy (pullS hell hdvd F) = coarseCurlEnergy hdvd F := by
  unfold curlEnergy coarseCurlEnergy
  rw [Finset.sum_congr rfl (fun p _ => by rw [flatCurl_pullS hell hdvd F p])]
  exact Fintype.sum_equiv (cpEquiv hell hdvd).symm _ _ (fun _ => rfl)

section Axioms1
#print axioms cbToBond
#print axioms bondToCb
#print axioms cbEquiv
#print axioms cpToPlaq
#print axioms plaqToCp
#print axioms cpEquiv
#print axioms pullS
#print axioms pullS_apply
#print axioms pullS_add
#print axioms pullS_smul
#print axioms cEnergy
#print axioms coarseCurlEnergy
#print axioms coarseCurlEnergy_nonneg
#print axioms bondEnergy_pullS
#print axioms flatCurl_pullS
#print axioms curlEnergy_pullS
end Axioms1

/-! ## §2 — `VSrc`: CMP99b p.428's THREE CLAUSES

At `ell = 2` on the fine lattice and `ell = 2` again at the coarse level, so `Λ'` is the
`4`-sublattice of `L` and the standing divisibility hypothesis is `4 ∣ L μ + 1`. -/

theorem two_pos' : (0 : ℕ) < 2 := by norm_num

theorem two_dvd_of_four (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1) := by
  intro μ
  obtain ⟨m, hm⟩ := hdvd4 μ
  exact ⟨2 * m, by omega⟩

/-- The coarse lattice is itself `2`-compatible — this is where `4 ∣ L μ + 1` is spent. -/
theorem coarse_two_dvd (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent L 2 μ + 1) := by
  intro μ
  have hspec := coarseExtent_spec (L := L) (ell := 2) two_pos' (two_dvd_of_four hdvd4) μ
  obtain ⟨m, hm⟩ := hdvd4 μ
  exact ⟨m, by omega⟩

/-- The coarse extent has room for a nondegenerate block in every direction — also spent from
`4 ∣ L μ + 1`. Needed so `Ax(y)` is not empty at the origin. -/
theorem coarse_extent_pos (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (μ : Fin 3) :
    1 < coarseExtent L 2 μ + 1 := by
  have hspec := coarseExtent_spec (L := L) (ell := 2) two_pos' (two_dvd_of_four hdvd4) μ
  obtain ⟨m, hm⟩ := hdvd4 μ
  omega

/-- The pullback used throughout: a coarse field of `L` at scale `2`, read as a bond field on the
coarse lattice regarded as a periodic lattice in its own right. -/
noncomputable def pullC (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (B : CoarseBond L 2 → SuTwo) : Bond (coarseExtent L 2) → SuTwo :=
  pullS two_pos' (two_dvd_of_four hdvd4) B

theorem pullC_apply (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (B : CoarseBond L 2 → SuTwo) (e : Bond (coarseExtent L 2)) :
    pullC hdvd4 B e = B (bondToCb two_pos' (two_dvd_of_four hdvd4) e) := rfl

/-- **CMP99b p.428's SUBSPACE, all three clauses, in the source's order.**

`{B : B = 0 on Λᶜ, B = 0 on ⋃_{y ∈ Λ'} Ax(y), Q₁B = 0}`.

* `(c1)` is `True` here — the carrier is the periodic torus, `Λᶜ = ∅`. Carried explicitly so the
  clause count matches the source; see the module header for why this makes every result below
  weaker, never stronger.
* `(c2)` is the bond-form axial locus `AxialContour.Ax` at the coarse lattice, centres `Λ'` = the
  coarse lattice's own `2`-sublattice.
* `(c3)` is `Q₁ = lineCoarseRestrictCov (trivialU) 2` at the coarse lattice (see the header's
  scope note on which `Q₁`). -/
def VSrc (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (B : CoarseBond L 2 → SuTwo) : Prop :=
  True
  ∧ (∀ y ∈ CoarseLattice (coarseExtent L 2) 2, ∀ b ∈ Ax y 2, pullC hdvd4 B b = 0)
  ∧ (∀ c : CoarseBond (coarseExtent L 2) 2,
      AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov
        (trivialU (coarseExtent L 2)) 2 (pullC hdvd4 B) c = 0)

/-- `VSrc` is a linear condition: it contains `0`. (Anti-vacuity in the other direction is §3b.) -/
theorem VSrc_zero (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    VSrc hdvd4 (fun _ : CoarseBond L 2 => (0 : SuTwo)) := by
  refine ⟨trivial, fun y _ b _ => rfl, fun c => ?_⟩
  have hz : pullC hdvd4 (fun _ : CoarseBond L 2 => (0 : SuTwo))
      = (0 : Bond (coarseExtent L 2) → SuTwo) := rfl
  have hmap := map_zero (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCovLM
    (trivialU (coarseExtent L 2)) 2)
  rw [hz]
  exact congrFun hmap c

/-! ## §3 — THE HINGE: `VSrc` EXCLUDES THE WHOLE EXTREMAL FAMILY

`OnRangeCoercivity` §5d proves the wall is the family `{siteConstCoarse g : g ≠ 0}` — every nonzero
site-constant coarse mode is the coarse datum of an extremal vector, so a `V` rescues the route only
by excluding all of them. `VSrc` does, **by clause (c2) alone**: `Ax(y)` contains a bond of every
direction whose block is nondegenerate, and a site-constant mode is `g ρ ≠ 0` on every direction-`ρ`
bond. So the hinge is independent of the `Q₁` reading. -/

/-- The pullback of a site-constant coarse mode is the site-constant field of the coarse lattice —
the direction component is untouched by the reindexing, so this is definitional. -/
theorem pullC_siteConstCoarse (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (g : Fin 3 → SuTwo) :
    pullC hdvd4 (AdalyFormal.Balaban.OnRangeCoercivity.siteConstCoarse (L := L) g)
      = fun e : Bond (coarseExtent L 2) => g e.2 := rfl

/-- **THE EXCLUSION THEOREM.** No nonzero site-constant coarse mode lies in `VSrc`. -/
theorem siteConst_not_VSrc (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {g : Fin 3 → SuTwo} {ρ : Fin 3} (hg : g ρ ≠ 0) :
    ¬ VSrc hdvd4 (AdalyFormal.Balaban.OnRangeCoercivity.siteConstCoarse (L := L) g) := by
  rintro ⟨-, hc2, -⟩
  -- the origin of the coarse lattice, and its `ρ`-neighbour inside the origin block
  have hy : AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent L 2)
      ∈ CoarseLattice (coarseExtent L 2) 2 :=
    AdalyFormal.Balaban.FibreCoercivity.zeroSite_coarse
  set y : PeriodicLatticeSite (coarseExtent L 2) :=
    AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent L 2) with hydef
  set x : PeriodicLatticeSite (coarseExtent L 2) :=
    Function.update y ρ ⟨1, coarse_extent_pos hdvd4 ρ⟩ with hxdef
  have hxρ : (x ρ).val = 1 := by rw [hxdef, Function.update_self]
  have hxne : ∀ ν : Fin 3, ν ≠ ρ → (x ν).val = 0 := by
    intro ν hν
    rw [hxdef, Function.update_of_ne hν, hydef]
    rfl
  have hyval : ∀ ν : Fin 3, (y ν).val = 0 := fun ν => rfl
  have hxmem : x ∈ blockOf y 2 := by
    rw [mem_blockOf]
    intro ν
    by_cases h : ν = ρ
    · subst h; rw [hyval, hxρ]; omega
    · rw [hyval, hxne ν h]; omega
  have hxney : x ≠ y := by
    intro h
    have : (x ρ).val = (y ρ).val := by rw [h]
    rw [hxρ, hyval] at this
    omega
  have hdirne : y ρ ≠ x ρ := by
    intro h
    have : (y ρ).val = (x ρ).val := by rw [h]
    rw [hxρ, hyval] at this
    omega
  obtain ⟨b, hb, hbdir⟩ :=
    AdalyFormal.Balaban.HarmonicModes.staircasePath_exists_dir_of_ne y x ρ hdirne
  have hbax : b ∈ Ax y 2 := mem_Ax.2 ⟨x, hxmem, hxney, hb⟩
  have hzero := hc2 y hy b hbax
  rw [pullC_siteConstCoarse] at hzero
  exact hg (by rw [← hbdir]; exact hzero)

section Axioms3
#print axioms two_pos'
#print axioms two_dvd_of_four
#print axioms coarse_two_dvd
#print axioms coarse_extent_pos
#print axioms pullC
#print axioms pullC_apply
#print axioms VSrc
#print axioms VSrc_zero
#print axioms pullC_siteConstCoarse
#print axioms siteConst_not_VSrc
end Axioms3

/-! ## §4 — THE COARSE FIBRE BOUND ON `VSrc`

`FibreAggregate.aggregate_fibre_bound_gamma` is a theorem at EVERY periodic extent. Instantiated at
`coarseExtent L 2` — the coarse lattice as a lattice in its own right, §1 — on the transported
field, with clause `(c3)` supplying its `Q`-hypothesis and clause `(c2)` killing its `pAx` term, it
becomes a POINCARÉ INEQUALITY FOR THE COARSE FIELD with the same `L`-free constant
`γ_agg = 1/3316224`. Nothing here is new analysis; the content is that the source's own subspace is
exactly the hypothesis set of a theorem this tree already owns, one level up. -/

theorem pullC_eq (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (B : CoarseBond L 2 → SuTwo) :
    pullC hdvd4 B = pullS two_pos' (two_dvd_of_four hdvd4) B := rfl

/-- **`γ_agg‖B‖² ≤ coarseCurlEnergy B` FOR EVERY `B ∈ VSrc`.** -/
theorem coarse_fibre_bound_on_VSrc (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {B : CoarseBond L 2 → SuTwo} (hB : VSrc hdvd4 B) :
    AdalyFormal.Balaban.FibreAggregate.gammaAgg * cEnergy B
      ≤ coarseCurlEnergy (two_dvd_of_four hdvd4) B := by
  obtain ⟨-, hc2, hc3⟩ := hB
  have hfib := AdalyFormal.Balaban.FibreAggregate.aggregate_fibre_bound_gamma
    (L := coarseExtent L 2) (coarse_two_dvd hdvd4) (pullC hdvd4 B) hc3
  rw [AdalyFormal.Balaban.FibreCoercivity.deltaK_trivialU_eq_curlEnergy] at hfib
  have hpax : pAx (pullC hdvd4 B) (CoarseLattice (coarseExtent L 2) 2) 2 = 0 :=
    pAx_eq_zero_of_vanishing_on_Ax _ _ _ hc2
  rw [hpax, add_zero, pullC_eq, bondEnergy_pullS, curlEnergy_pullS] at hfib
  exact hfib

/-! ## §5 — STOKES: the coarse curl energy of a block average is dominated by the fine curl energy

`ThirdLevelStokes.stokes_flat` is the exact identity `∂₁' ∘ Q_ell = P_ell ∘ d` at `U = 1`, for every
`ell` and every compatible torus. Cauchy–Schwarz on its `ell⁵` summands, the block partition
(`StridedAveraging.coarseLattice_eq_biUnion` at stride `1`) and translation invariance of the
plaquette sum turn it into the energy inequality `coarseCurlEnergy (Q v) ≤ ell⁻¹ · curlEnergy v`.

The `ell⁻¹` is not tuned: it is `ell⁵` (Cauchy–Schwarz count) `× ell⁻⁸` (the square of `stokes_flat`'s
own `ell⁻⁴` normalisation) `× ell²` (each fine plaquette is hit once per `(i,j)` offset). -/

section StokesEnergy

open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.StridedAveraging (coarseLattice_eq_biUnion stepBlockOf_pairwise_disjoint
  mem_coarseLattice_one stepPathSite_one_stride stepPathSite_injective)

/-- The block partition of the fine lattice, as a summation law. Stride-`1` instance of
`StridedAveraging.coarseLattice_eq_biUnion`; no new combinatorics. -/
theorem sum_over_blocks {M : Type*} [AddCommMonoid M] (hell : 0 < ell)
    (f : PeriodicLatticeSite L → M) :
    ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, f x
      = ∑ x : PeriodicLatticeSite L, f x := by
  classical
  have hm : 0 < 1 * ell := by omega
  have hpart := coarseLattice_eq_biUnion (L := L) (s := 1) (ell := ell) hm
  rw [one_mul] at hpart
  have hdisj : (CoarseLattice L ell : Set (PeriodicLatticeSite L)).PairwiseDisjoint
      (fun c => stepBlockOf c 1 ell) := by
    intro c hc c' hc' hne
    exact stepBlockOf_pairwise_disjoint (L := L) (s := 1) (ell := ell)
      (by rw [one_mul]; exact hc) (by rw [one_mul]; exact hc') hne
  have huniv : (Finset.univ : Finset (PeriodicLatticeSite L)) = CoarseLattice L 1 :=
    (Finset.eq_univ_of_forall (fun z => mem_coarseLattice_one z)).symm
  rw [huniv, hpart, Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl (fun c _ => by rw [stepBlockOf_one])

/-- Translation invariance of a sum over all sites: `x ↦ x + i e_μ + j e_ν` is a bijection. -/
theorem sum_shift_invariant {M : Type*} [AddCommMonoid M] (μ ν : Fin 3) (i j : ℕ)
    (f : PeriodicLatticeSite L → M) :
    ∑ x : PeriodicLatticeSite L, f (pathSite (pathSite x μ i) ν j)
      = ∑ x : PeriodicLatticeSite L, f x := by
  have hinj1 : Function.Injective (fun x : PeriodicLatticeSite L => pathSite x μ i) := by
    intro a b h
    refine stepPathSite_injective (L := L) 1 μ i ?_
    rw [stepPathSite_one_stride, stepPathSite_one_stride]
    exact h
  have hinj2 : Function.Injective (fun x : PeriodicLatticeSite L => pathSite x ν j) := by
    intro a b h
    refine stepPathSite_injective (L := L) 1 ν j ?_
    rw [stepPathSite_one_stride, stepPathSite_one_stride]
    exact h
  have hinj : Function.Injective
      (fun x : PeriodicLatticeSite L => pathSite (pathSite x μ i) ν j) :=
    Function.Injective.comp hinj2 hinj1
  exact Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp hinj) _ _ (fun _ => rfl)

/-- **PER-PLAQUETTE CAUCHY–SCHWARZ ON `stokes_flat`.** -/
theorem coarseCurl_sq_le (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (v : Bond L → SuTwo) (q : CoarsePlaquette L ell) :
    ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCov (trivialU L) ell v) q‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 3) *
        ∑ x ∈ blockOf q.1.1 ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ‖flatCurlValue v (pathSite (pathSite x q.2.1.1 i) q.2.1.2 j, q.2)‖ ^ 2 := by
  classical
  obtain ⟨⟨y, hy⟩, d⟩ := q
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set S : Finset (PeriodicLatticeSite L × ℕ × ℕ) :=
    (blockOf y ell) ×ˢ ((Finset.range ell) ×ˢ (Finset.range ell)) with hS
  set f : PeriodicLatticeSite L × ℕ × ℕ → SuTwo :=
    fun t => flatCurlValue v (pathSite (pathSite t.1 d.1.1 t.2.1) d.1.2 t.2.2, d) with hf
  -- `stokes_flat`, with the flat curl substituted for the `U = 1` covariant one
  have hstokes : ∑ t ∈ S, f t
      = ((ell : ℝ) ^ 4) •
        coarseCurlSuTwo hdvd (lineCoarseRestrictCov (trivialU L) ell v) ((⟨y, hy⟩, d)) := by
    have hsf := AdalyFormal.Balaban.ThirdLevelStokes.stokes_flat hell hdvd hy d.2 v
    rw [hS, Finset.sum_product]
    have hin : ∀ x ∈ blockOf y ell,
        (∑ p ∈ (Finset.range ell) ×ˢ (Finset.range ell), f (x, p))
          = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
              AdalyFormal.Balaban.CovariantOperators.curlValueCovariant (trivialU L) v
                (pathSite (pathSite x d.1.1 i) d.1.2 j, d) := by
      intro x _
      rw [Finset.sum_product (Finset.range ell) (Finset.range ell) (fun p : ℕ × ℕ => f (x, p))]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        (congrFun (AdalyFormal.Balaban.CovU1Reduction.curlValueCovariant_trivialU_eq v) _).symm))
    rw [Finset.sum_congr rfl hin]
    exact hsf
  -- the count
  have hcard : (S.card : ℝ) = (ell : ℝ) ^ 5 := by
    rw [hS, Finset.card_product, Finset.card_product, Finset.card_range,
      AdalyFormal.Balaban.AdmissibleSubspace.card_blockOf y ell
        (AdalyFormal.Balaban.AdmissibleSubspace.coarseLattice_mem_fits hdvd hy)]
    push_cast
    ring
  -- triangle + Cauchy-Schwarz
  have htri : ‖∑ t ∈ S, f t‖ ≤ ∑ t ∈ S, ‖f t‖ := norm_sum_le _ _
  have hcs : (∑ t ∈ S, ‖f t‖) ^ 2 ≤ (S.card : ℝ) * ∑ t ∈ S, ‖f t‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hWsq : ‖∑ t ∈ S, f t‖ ^ 2 ≤ (ell : ℝ) ^ 5 * ∑ t ∈ S, ‖f t‖ ^ 2 := by
    have h1 : ‖∑ t ∈ S, f t‖ ^ 2 ≤ (∑ t ∈ S, ‖f t‖) ^ 2 := by
      have hnn : (0 : ℝ) ≤ ∑ t ∈ S, ‖f t‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      nlinarith [norm_nonneg (∑ t ∈ S, f t)]
    rw [← hcard]
    linarith
  -- transfer through `stokes_flat`
  have hnormW : ‖∑ t ∈ S, f t‖ ^ 2
      = ((ell : ℝ) ^ 8) *
        ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCov (trivialU L) ell v) ((⟨y, hy⟩, d))‖ ^ 2 := by
    rw [hstokes, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ell:ℝ)^4)]
    ring
  have hSsq : ∑ t ∈ S, ‖f t‖ ^ 2
      = ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ‖flatCurlValue v (pathSite (pathSite x d.1.1 i) d.1.2 j, d)‖ ^ 2 := by
    rw [hS, Finset.sum_product]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_product (Finset.range ell)
      (Finset.range ell) (fun p : ℕ × ℕ => ‖f (x, p)‖ ^ 2))
  rw [hnormW, hSsq] at hWsq
  have hpow : (ell : ℝ) ^ 8 = (ell : ℝ) ^ 5 * (ell : ℝ) ^ 3 := by ring
  rw [hpow] at hWsq
  have h5 : (0 : ℝ) < (ell : ℝ) ^ 5 := by positivity
  have h3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  rw [one_div, inv_mul_eq_div, le_div_iff₀ h3]
  refine le_of_mul_le_mul_left ?_ h5
  have hre : (ell : ℝ) ^ 5 *
      (‖coarseCurlSuTwo hdvd (lineCoarseRestrictCov (trivialU L) ell v) ((⟨y, hy⟩, d))‖ ^ 2
        * (ell : ℝ) ^ 3)
      = (ell : ℝ) ^ 5 * (ell : ℝ) ^ 3 *
        ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCov (trivialU L) ell v) ((⟨y, hy⟩, d))‖ ^ 2 := by
    ring
  rw [hre]
  exact hWsq

/-- **THE STOKES ENERGY BOUND.** `coarseCurlEnergy (Q_ell v) ≤ ell⁻¹ · curlEnergy v`, at `U = 1`,
for every `ell > 0` and every compatible torus. -/
theorem coarseCurlEnergy_Q_le (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (v : Bond L → SuTwo) :
    coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU L) ell v)
      ≤ (1 / (ell : ℝ)) * curlEnergy v := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  -- step 1: sum the per-plaquette bound
  have h1 : coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU L) ell v)
      ≤ ∑ q : CoarsePlaquette L ell, (1 / (ell : ℝ) ^ 3) *
          ∑ x ∈ blockOf q.1.1 ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
            ‖flatCurlValue v (pathSite (pathSite x q.2.1.1 i) q.2.1.2 j, q.2)‖ ^ 2 :=
    Finset.sum_le_sum (fun q _ => coarseCurl_sq_le hell hdvd v q)
  -- step 2: evaluate the right-hand side exactly
  have h2 : ∑ q : CoarsePlaquette L ell, (1 / (ell : ℝ) ^ 3) *
        ∑ x ∈ blockOf q.1.1 ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ‖flatCurlValue v (pathSite (pathSite x q.2.1.1 i) q.2.1.2 j, q.2)‖ ^ 2
      = (1 / (ell : ℝ)) * curlEnergy v := by
    rw [← Finset.mul_sum]
    have hsplit : ∑ q : CoarsePlaquette L ell,
        (∑ x ∈ blockOf q.1.1 ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ‖flatCurlValue v (pathSite (pathSite x q.2.1.1 i) q.2.1.2 j, q.2)‖ ^ 2)
        = ∑ d : PeriodicPlaquetteDirections,
            ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell,
              ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
                ‖flatCurlValue v (pathSite (pathSite x d.1.1 i) d.1.2 j, d)‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl) (fun y =>
        ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ‖flatCurlValue v (pathSite (pathSite x d.1.1 i) d.1.2 j, d)‖ ^ 2)).symm
    rw [hsplit]
    have hblocks : ∀ d : PeriodicPlaquetteDirections,
        ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell,
            ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
              ‖flatCurlValue v (pathSite (pathSite x d.1.1 i) d.1.2 j, d)‖ ^ 2
          = (ell : ℝ) ^ 2 * ∑ x : PeriodicLatticeSite L, ‖flatCurlValue v (x, d)‖ ^ 2 := by
      intro d
      rw [sum_over_blocks hell]
      rw [Finset.sum_comm]
      have hij : ∀ i ∈ Finset.range ell,
          ∑ x : PeriodicLatticeSite L, ∑ j ∈ Finset.range ell,
              ‖flatCurlValue v (pathSite (pathSite x d.1.1 i) d.1.2 j, d)‖ ^ 2
            = (ell : ℝ) * ∑ x : PeriodicLatticeSite L, ‖flatCurlValue v (x, d)‖ ^ 2 := by
        intro i _
        rw [Finset.sum_comm]
        have hj : ∀ j ∈ Finset.range ell,
            ∑ x : PeriodicLatticeSite L,
                ‖flatCurlValue v (pathSite (pathSite x d.1.1 i) d.1.2 j, d)‖ ^ 2
              = ∑ x : PeriodicLatticeSite L, ‖flatCurlValue v (x, d)‖ ^ 2 := by
          intro j _
          exact sum_shift_invariant d.1.1 d.1.2 i j
            (fun z => ‖flatCurlValue v (z, d)‖ ^ 2)
        rw [Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hij, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun d _ => hblocks d)]
    rw [← Finset.mul_sum]
    have hce : ∑ d : PeriodicPlaquetteDirections,
        ∑ x : PeriodicLatticeSite L, ‖flatCurlValue v (x, d)‖ ^ 2 = curlEnergy v := by
      unfold curlEnergy
      rw [Fintype.sum_prod_type]
      exact (Finset.sum_comm).symm
    rw [hce]
    field_simp
  linarith [h1, h2.le, h2.ge]

end StokesEnergy

/-! ## §6 — THE DESCENT: a POSITIVE bound on the source's subspace

`ExtentUniformCoercivity.master_defect_bound_sharp` is unconditional at the tree's own operators:
`E ≤ 13264896·D + 6632448·P + 13583253568·C` with `E = bondEnergy A`, `D = curlEnergy A`,
`P = pAx A`, `C = coarseEnergy (Q A)`. §4 and §5 bound `C` by `D`:
`C ≤ γ_agg⁻¹ · coarseCurlEnergy (Q A) ≤ 3316224 · (1/2) · D = 1658112·D`. -/

/-- `γ_V = 1 / (13264896 + 13583253568 · 3316224 / 2)`, every factor counted:
`13264896` and `13583253568` from the master defect bound, `3316224 = γ_agg⁻¹` from the coarse fibre
bound, `1/2 = ell⁻¹` at `ell = 2` from Stokes. -/
noncomputable def gammaV : ℝ := 1 / 22522555753408512

theorem gammaV_pos : 0 < gammaV := by
  rw [gammaV]; norm_num

/-- **THE POSITIVE COERCIVITY BOUND ON THE SOURCE'S SUBSPACE.** For EVERY fine field whose coarse
datum lies in `VSrc`, the gauge-fixed form is coercive with an explicit `L`-free constant. This is
strictly stronger than what `next_coercive_gf_on_subspace` consumes: it holds on the whole preimage
`Q⁻¹(VSrc)`, not merely on `H₁(VSrc) = G(Q*(S VSrc))`. -/
theorem coercive_on_VSrc_preimage (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hA : VSrc hdvd4 (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov
      (trivialU L) 2 A)) :
    gammaV * bondEnergy A ≤ curlEnergy A + pAx A (CoarseLattice L 2) 2 := by
  have hdvd2 := two_dvd_of_four hdvd4
  set Fc := AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov (trivialU L) 2 A
    with hFc
  -- (a) the master defect bound
  have hm := AdalyFormal.Balaban.ExtentUniformCoercivity.master_defect_bound_sharp hdvd2 A
  -- (b) the coarse fibre bound on `VSrc`
  have hfib := coarse_fibre_bound_on_VSrc hdvd4 hA
  rw [AdalyFormal.Balaban.FibreAggregate.gammaAgg] at hfib
  -- (c) Stokes
  have hst := coarseCurlEnergy_Q_le (L := L) (ell := 2) (by norm_num) hdvd2 A
  rw [← hFc] at hst
  -- `cEnergy` at `ell = 2` IS `coarseEnergy`
  have hcE : cEnergy Fc = AdalyFormal.Balaban.ExtentUniformCoercivity.coarseEnergy Fc := rfl
  rw [hcE] at hfib
  have hnum : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hnum] at hst
  have hD : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 :=
    AdalyFormal.Balaban.AxialCoercivity.pAx_nonneg A (CoarseLattice L 2) 2
  have hC : AdalyFormal.Balaban.ExtentUniformCoercivity.coarseEnergy Fc ≤ 1658112 * curlEnergy A := by
    nlinarith [hfib, hst]
  rw [gammaV]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 22522555753408512)]
  nlinarith [hm, hC, hD, hP]

/-! ## §7 — ANTI-VACUITY: `VSrc` CONTAINS A NONZERO ELEMENT

§6's bound would say nothing if `VSrc = {0}`. It is not. The witness is explicit and its two
clauses are discharged by two INDEPENDENT mechanisms, neither of them a counting argument:

* **(c2) by the source's own contour geometry.** `AxialCoercivity.staircasePath_coord_zero` —
  "coordinate `0` is pinned to `y₀` on every non-direction-`0` bond of `Γ_{y,x}`" — says every
  direction-`1` bond of `Ax(y)` sits at an EVEN `0`-coordinate (`y ∈ Λ'`). The witness is supported
  on direction-`1` bonds at ODD `0`-coordinate, so it vanishes on the whole axial locus.
* **(c3) POINTWISE, not by cancellation over a block.** The `Q₁`-average is a sum of length-`2`
  line integrals in direction `1`; a shift in direction `1` does not move the `0`-coordinate, so
  each individual line integral is `(±1 ∓ 1)·w = 0` on its own. The alternation is in the
  `1`-coordinate, which is exactly the direction the line integral runs along.

The wrap-around case (`x₁ + 1 = L₁ + 1`) is where `2 ∣ (coarseExtent L 2 μ + 1)` is spent: the
alternation must close up on the torus, and it does precisely because the coarse extent is even. -/

section Witness

open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.U1AnchorPoincare (shift_val shift_apply_ne)

/-- `+1` on even `0`-coordinates of direction-`1` bonds at ODD `1`... -/
noncomputable def wSign {Lc : PeriodicLatticeExtent} (b : Bond Lc) : ℝ :=
  if b.2 = 1 ∧ (b.1 0).val % 2 = 1 then (if (b.1 1).val % 2 = 0 then (1 : ℝ) else -1) else 0

/-- **THE WITNESS FIELD**, on the coarse lattice read as a lattice in its own right. -/
noncomputable def vWitFine {Lc : PeriodicLatticeExtent} (w : SuTwo) : Bond Lc → SuTwo :=
  fun b => wSign b • w

theorem wSign_of_dir_ne {Lc : PeriodicLatticeExtent} {b : Bond Lc} (h : b.2 ≠ 1) :
    wSign b = 0 := by
  unfold wSign
  rw [if_neg (fun hc => h hc.1)]

theorem wSign_of_even {Lc : PeriodicLatticeExtent} {b : Bond Lc} (h : (b.1 0).val % 2 = 0) :
    wSign b = 0 := by
  unfold wSign
  refine if_neg (fun hc => ?_)
  omega

/-- **(c2).** The witness vanishes on the whole coarse axial locus. -/
theorem vWitFine_vanishes_on_Ax {Lc : PeriodicLatticeExtent} (w : SuTwo)
    {y : PeriodicLatticeSite Lc} (hy : y ∈ CoarseLattice Lc 2) {b : Bond Lc} (hb : b ∈ Ax y 2) :
    vWitFine (Lc := Lc) w b = 0 := by
  unfold vWitFine
  by_cases hd : b.2 = 1
  · -- direction `1`: `staircasePath_coord_zero` pins the `0`-coordinate to `y₀`, which is even
    obtain ⟨x, -, -, hbs⟩ := mem_Ax.1 hb
    have h0 : b.1 0 = y 0 :=
      AdalyFormal.Balaban.AxialCoercivity.staircasePath_coord_zero hbs (by rw [hd]; decide)
    have hyeven : (y 0).val % 2 = 0 := mem_CoarseLattice.1 hy 0
    rw [wSign_of_even (by rw [h0]; exact hyeven), zero_smul]
  · rw [wSign_of_dir_ne hd, zero_smul]

/-- The value of the sign at a direction-`1` bond based at an ODD `0`-coordinate. -/
theorem wSign_dir_one {Lc : PeriodicLatticeExtent} (x : PeriodicLatticeSite Lc)
    (hodd : (x 0).val % 2 = 1) :
    wSign ((x, (1 : Fin 3)) : Bond Lc) = if (x 1).val % 2 = 0 then (1 : ℝ) else -1 := by
  unfold wSign
  rw [if_pos ⟨rfl, hodd⟩]

/-- The alternation closes up on an EVEN extent: consecutive `1`-coordinates always carry opposite
signs, wrap-around included. -/
theorem wSign_line_cancel {Lc : PeriodicLatticeExtent} (heven : (2 : ℕ) ∣ (Lc 1 + 1))
    (x : PeriodicLatticeSite Lc) :
    wSign ((x, (1 : Fin 3)) : Bond Lc)
      + wSign ((periodicLatticeShift x 1, (1 : Fin 3)) : Bond Lc) = 0 := by
  have h0 : ((periodicLatticeShift x 1) 0) = x 0 := shift_apply_ne x 1 0 (by decide)
  have h1 : ((periodicLatticeShift x 1) 1).val = ((x 1).val + 1) % (Lc 1 + 1) := shift_val x 1
  by_cases hodd : (x 0).val % 2 = 1
  · have hs0 := wSign_dir_one (Lc := Lc) x hodd
    have hs1 := wSign_dir_one (Lc := Lc) (periodicLatticeShift x 1) (by rw [h0]; exact hodd)
    have hflip : ((periodicLatticeShift x 1) 1).val % 2 = ((x 1).val + 1) % 2 := by
      rw [h1]
      obtain ⟨m, hm⟩ := heven
      rcases Nat.lt_or_ge ((x 1).val + 1) (Lc 1 + 1) with h | h
      · rw [Nat.mod_eq_of_lt h]
      · have hxe : (x 1).val + 1 = Lc 1 + 1 := by have := (x 1).isLt; omega
        rw [hxe, Nat.mod_self]
        omega
    rw [hs0, hs1, hflip]
    by_cases hp : (x 1).val % 2 = 0
    · rw [if_pos hp, if_neg (by omega)]; ring
    · rw [if_neg hp, if_pos (by omega)]; ring
  · have h2 : (x 0).val % 2 = 0 := by omega
    rw [wSign_of_even (Lc := Lc) (b := ((x, (1 : Fin 3)) : Bond Lc)) h2,
      wSign_of_even (Lc := Lc) (b := ((periodicLatticeShift x 1, (1 : Fin 3)) : Bond Lc))
        (by show ((periodicLatticeShift x 1) 0).val % 2 = 0; rw [h0]; exact h2)]
    ring

/-- **(c3).** Every length-`2` line integral of the witness vanishes, pointwise. -/
theorem vWitFine_lineSum_zero {Lc : PeriodicLatticeExtent} (heven : (2 : ℕ) ∣ (Lc 1 + 1))
    (w : SuTwo) (x : PeriodicLatticeSite Lc) (μ : Fin 3) :
    AdalyFormal.Balaban.ThirdLevelStokes.lineSum 2 (vWitFine (Lc := Lc) w) x μ = 0 := by
  unfold AdalyFormal.Balaban.ThirdLevelStokes.lineSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  by_cases hd : μ = 1
  · subst hd
    have e0 : pathSite x 1 0 = x := pathSite_zero x 1
    have e1 : pathSite x 1 1 = periodicLatticeShift x 1 := by
      rw [pathSite_succ, pathSite_zero]
    rw [e0, e1]
    show wSign (x, (1 : Fin 3)) • w + wSign (periodicLatticeShift x 1, (1 : Fin 3)) • w = 0
    rw [← add_smul, wSign_line_cancel heven x, zero_smul]
  · show wSign _ • w + wSign _ • w = 0
    rw [wSign_of_dir_ne (Lc := Lc) (b := (pathSite x μ 0, μ)) hd,
      wSign_of_dir_ne (Lc := Lc) (b := (pathSite x μ 1, μ)) hd, zero_smul, add_zero]

/-- **(c3), assembled**: `Q₁` of the witness vanishes at every coarse bond. -/
theorem vWitFine_Q_zero {Lc : PeriodicLatticeExtent} (heven : (2 : ℕ) ∣ (Lc 1 + 1))
    (w : SuTwo) (c : CoarseBond Lc 2) :
    AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov (trivialU Lc) 2
      (vWitFine (Lc := Lc) w) c = 0 := by
  have h := AdalyFormal.Balaban.ThirdLevelStokes.ell4_smul_lineCoarseRestrict
    (L := Lc) 2 two_pos' (vWitFine (Lc := Lc) w) c
  rw [Finset.sum_congr rfl (fun x _ => vWitFine_lineSum_zero heven w x c.2)] at h
  rw [Finset.sum_const_zero] at h
  have h16 : ((2 : ℕ) : ℝ) ^ 4 ≠ 0 := by norm_num
  have := smul_eq_zero.1 h
  rcases this with hz | hz
  · exact absurd hz h16
  · exact hz

/-- The coarse field on `L` whose transport is the witness. -/
noncomputable def vWitCoarse (_hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (w : SuTwo) :
    CoarseBond L 2 → SuTwo :=
  fun c => vWitFine (Lc := coarseExtent L 2) w (cbToBond L 2 c)

theorem pullC_vWitCoarse (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (w : SuTwo) :
    pullC hdvd4 (vWitCoarse hdvd4 w) = vWitFine (Lc := coarseExtent L 2) w := by
  funext e
  show vWitFine (Lc := coarseExtent L 2) w
      (cbToBond L 2 (bondToCb two_pos' (two_dvd_of_four hdvd4) e)) = _
  exact congrArg (vWitFine (Lc := coarseExtent L 2) w)
    ((cbEquiv two_pos' (two_dvd_of_four hdvd4)).right_inv e)

/-- **THE WITNESS IS IN `VSrc`.** -/
theorem vWitCoarse_mem_VSrc (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (w : SuTwo) :
    VSrc hdvd4 (vWitCoarse hdvd4 w) := by
  refine ⟨trivial, ?_, ?_⟩
  · intro y hy b hb
    rw [pullC_vWitCoarse]
    exact vWitFine_vanishes_on_Ax w hy hb
  · intro c
    rw [pullC_vWitCoarse]
    exact vWitFine_Q_zero (coarse_two_dvd hdvd4 1) w c

/-- The site with `0`-coordinate `1` and every other coordinate `0`, on the coarse lattice.
`4 ∣ L μ + 1` is what supplies it (`coarse_extent_pos`). -/
noncomputable def witSite (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    PeriodicLatticeSite (coarseExtent L 2) :=
  Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent L 2)) 0
    ⟨1, coarse_extent_pos hdvd4 0⟩

/-- **THE WITNESS TAKES THE VALUE `w` AT A NAMED BOND.** Not an opaque existence statement: the
coarse bond is exhibited and the value computed. -/
theorem vWitCoarse_value (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (w : SuTwo) :
    vWitCoarse hdvd4 w
        (bondToCb two_pos' (two_dvd_of_four hdvd4) ((witSite hdvd4, (1 : Fin 3)))) = w := by
  have hz0 : ((witSite hdvd4) 0).val = 1 := by
    show (Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent L 2)) 0
      (⟨1, coarse_extent_pos hdvd4 0⟩ : Fin (coarseExtent L 2 0 + 1)) 0).val = 1
    rw [Function.update_self]
  have hz1 : ((witSite hdvd4) 1).val = 0 := by
    show (Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite (coarseExtent L 2)) 0
      (⟨1, coarse_extent_pos hdvd4 0⟩ : Fin (coarseExtent L 2 0 + 1)) 1).val = 0
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    rfl
  have hval : vWitFine (Lc := coarseExtent L 2) w ((witSite hdvd4, (1 : Fin 3))) = w := by
    unfold vWitFine wSign
    rw [if_pos ⟨rfl, by rw [hz0]⟩, if_pos (by rw [hz1]), one_smul]
  have hcong := congrFun (pullC_vWitCoarse hdvd4 w) ((witSite hdvd4, (1 : Fin 3)))
  rw [hval] at hcong
  exact hcong

/-- **AND IT IS NONZERO.** -/
theorem vWitCoarse_ne_zero (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) {w : SuTwo} (hw : w ≠ 0) :
    vWitCoarse hdvd4 w ≠ 0 := by
  intro hzero
  refine hw ?_
  rw [← vWitCoarse_value hdvd4 w, hzero]
  rfl

/-! ### `VSrc` is a LINEAR subspace

All three clauses are linear conditions, so `VSrc_nontrivial` is not "one lucky point": `VSrc`
contains the whole line through the witness. This closes the reading under which a `V` could be a
degenerate one-point set. -/

theorem VSrc_add (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {B B' : CoarseBond L 2 → SuTwo} (h : VSrc hdvd4 B) (h' : VSrc hdvd4 B') :
    VSrc hdvd4 (B + B') := by
  obtain ⟨-, h2, h3⟩ := h
  obtain ⟨-, h2', h3'⟩ := h'
  refine ⟨trivial, ?_, ?_⟩
  · intro y hy b hb
    show pullC hdvd4 B b + pullC hdvd4 B' b = 0
    rw [h2 y hy b hb, h2' y hy b hb, add_zero]
  · intro c
    have hsplit : pullC hdvd4 (B + B') = pullC hdvd4 B + pullC hdvd4 B' := rfl
    rw [hsplit, AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_add,
      h3 c, h3' c, add_zero]

theorem VSrc_smul (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (t : ℝ)
    {B : CoarseBond L 2 → SuTwo} (h : VSrc hdvd4 B) : VSrc hdvd4 (t • B) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨trivial, ?_, ?_⟩
  · intro y hy b hb
    show t • pullC hdvd4 B b = 0
    rw [h2 y hy b hb, smul_zero]
  · intro c
    have hsplit : pullC hdvd4 (t • B) = t • pullC hdvd4 B := rfl
    rw [hsplit, AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_smul, h3 c,
      smul_zero]

/-- **MUST-FIRE ON §4 AND §5's OWN OBJECTS.** The coarse curl energy of a `VSrc` element is
STRICTLY POSITIVE. So §4's inequality is not `0 ≤ 0`, and §5's upper bound is not an upper bound on
something identically zero. Proved by running §4 forwards on the §7 witness — a genuine second use
of the coarse fibre bound, not a restatement. -/
theorem witness_coarseCurl_pos (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) {w : SuTwo}
    (hw : w ≠ 0) :
    0 < coarseCurlEnergy (two_dvd_of_four hdvd4) (vWitCoarse hdvd4 w) := by
  have hfib := coarse_fibre_bound_on_VSrc hdvd4 (vWitCoarse_mem_VSrc hdvd4 w)
  have hcE : cEnergy (vWitCoarse hdvd4 w)
      = AdalyFormal.Balaban.ExtentUniformCoercivity.coarseEnergy (vWitCoarse hdvd4 w) := rfl
  rw [hcE] at hfib
  have hpos : 0 < AdalyFormal.Balaban.ExtentUniformCoercivity.coarseEnergy
      (vWitCoarse hdvd4 w) :=
    AdalyFormal.Balaban.OnRangeCoercivity.coarseEnergy_pos
      (c0 := bondToCb two_pos' (two_dvd_of_four hdvd4) ((witSite hdvd4, (1 : Fin 3))))
      (by rw [vWitCoarse_value]; exact hw)
  have hg := AdalyFormal.Balaban.FibreAggregate.gammaAgg_pos
  nlinarith

/-- **THE ANTI-VACUITY STATEMENT.** `VSrc` is a nondegenerate domain: it contains a nonzero
element, so §6's positive bound is not a statement about `{0}`. Paired with §3 (`VSrc` excludes the
entire extremal family) this brackets the subspace from both sides. -/
theorem VSrc_nontrivial (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    ∃ B : CoarseBond L 2 → SuTwo, VSrc hdvd4 B ∧ B ≠ 0 :=
  ⟨vWitCoarse hdvd4 AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
    vWitCoarse_mem_VSrc hdvd4 _,
    vWitCoarse_ne_zero hdvd4 AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero⟩

end Witness

section Axioms7
#print axioms wSign
#print axioms wSign_of_dir_ne
#print axioms wSign_of_even
#print axioms wSign_dir_one
#print axioms vWitFine
#print axioms vWitCoarse
#print axioms vWitFine_vanishes_on_Ax
#print axioms wSign_line_cancel
#print axioms vWitFine_lineSum_zero
#print axioms vWitFine_Q_zero
#print axioms pullC_vWitCoarse
#print axioms vWitCoarse_mem_VSrc
#print axioms witSite
#print axioms vWitCoarse_value
#print axioms vWitCoarse_ne_zero
#print axioms VSrc_add
#print axioms VSrc_smul
#print axioms witness_coarseCurl_pos
#print axioms VSrc_nontrivial
end Axioms7

/-! ## §8 — THE DOOR, OPEN: the one-step law holds on `VSrc`

§6 on the `L²` carrier, then fed into `OnRangeCoercivity.next_coercive_gf_on_subspace` — the
source-shaped restriction of the tower law. The result is the exact statement §5e of that module
said was missing: a POSITIVE coercivity constant on a NONTRIVIAL `H₁(V)`, with the source's own `V`.

Note what is *not* needed: `H₁ = G Q* S` never appears in §6's hypothesis. The bound holds on the
whole preimage `Q⁻¹(VSrc)`, of which `H₁(VSrc)` is a subset, so the one-step law gets it for free at
the only points it evaluates. -/

section Rung

open AdalyFormal.Balaban.TowerOneStep (Rung)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2 qCLM)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized)
open AdalyFormal.Balaban.AxialCoercivity (pAxCLM inner_pAxCLM_eq')
open AdalyFormal.Balaban.IslandBridge (norm_sq_bondFnL2)

/-- §6 on the `L²` carrier, in the exact `⟨x, Δx⟩ + ⟨x, Px⟩` shape the tower law consumes. -/
theorem coercive_on_VSrc_L2 (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (x : BondFnL2 L)
    (hx : VSrc hdvd4 (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov
      (trivialU L) 2 (WithLp.ofLp x))) :
    gammaV * ‖x‖ ^ 2
      ≤ (inner ℝ x (deltaKCLMNormalized (trivialU L) x) : ℝ)
        + (inner ℝ x (pAxCLM (CoarseLattice L 2) 2 x) : ℝ) := by
  have hb := coercive_on_VSrc_preimage hdvd4 (WithLp.ofLp x) hx
  have hnorm : ‖x‖ ^ 2 = bondEnergy (WithLp.ofLp x) := norm_sq_bondFnL2 (WithLp.ofLp x)
  have hD : (inner ℝ x (deltaKCLMNormalized (trivialU L) x) : ℝ) = curlEnergy (WithLp.ofLp x) :=
    AdalyFormal.Balaban.OnRangeCoercivity.inner_deltaK_flat x
  have hP : (inner ℝ x (pAxCLM (CoarseLattice L 2) 2 x) : ℝ)
      = pAx (WithLp.ofLp x) (CoarseLattice L 2) 2 := inner_pAxCLM_eq' _ _ x
  rw [hnorm, hD, hP]
  exact hb

/-- **THE ONE-STEP LAW ON THE SOURCE'S SUBSPACE.** For any rung at the tree's own flat operators,
the coarse-side conclusion holds for every `B ∈ VSrc`, with the explicit `L`-free constant
`γ_V / q²`. -/
theorem next_coercive_on_VSrc (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L)))
    (hP : r.P = pAxCLM (CoarseLattice L 2) 2) (hQ : r.Q = qCLM (trivialU L) 2)
    {B : CoarseFnL2 L 2} (hB : VSrc hdvd4 (WithLp.ofLp B)) :
    gammaV / r.q ^ 2 * ‖B‖ ^ 2 ≤ (inner ℝ B (r.next B) : ℝ) := by
  refine AdalyFormal.Balaban.OnRangeCoercivity.next_coercive_gf_on_subspace r gammaV_pos
    (fun C => VSrc hdvd4 (WithLp.ofLp C)) ?_ hB
  intro C hC
  set u : BondFnL2 L := r.G (r.Qstar (r.S C)) with hu
  -- the coarse datum of `u` IS `C`, so `u` lies in `Q⁻¹(VSrc)`
  have hQu : r.Q u = C := r.T_S C
  have hQfun : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov (trivialU L) 2
      (WithLp.ofLp u) = WithLp.ofLp C := by
    have h1 : (qCLM (trivialU L) 2 u : CoarseFnL2 L 2)
        = WithLp.toLp 2 (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov
          (trivialU L) 2 (WithLp.ofLp u)) := rfl
    have h2 : (qCLM (trivialU L) 2 u : CoarseFnL2 L 2) = C := by rw [← hQ]; exact hQu
    rw [h1] at h2
    exact congrArg WithLp.ofLp h2
  have hbound := coercive_on_VSrc_L2 hdvd4 u (by rw [hQfun]; exact hC)
  rw [hP]
  exact hbound

/-- **AND THE STATEMENT IS INHABITED BY A NONZERO POINT.** `VSrc` carries a nonzero `B` (§7), and
over a nonzero coarse datum the `H₁`-image is nonzero (`OnRangeCoercivity.range_elt_ne_zero`), so
`next_coercive_on_VSrc` is not a statement about `{0}` on either side. -/
theorem VSrc_carrier_nontrivial (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (r : Rung (BondFnL2 L) (CoarseFnL2 L 2) (deltaKCLMNormalized (trivialU L))) :
    ∃ B : CoarseFnL2 L 2, VSrc hdvd4 (WithLp.ofLp B) ∧ B ≠ 0
      ∧ r.G (r.Qstar (r.S B)) ≠ 0 := by
  obtain ⟨F, hF, hFne⟩ := VSrc_nontrivial hdvd4
  refine ⟨WithLp.toLp 2 F, hF, ?_, ?_⟩
  · intro h
    exact hFne (by
      have : (WithLp.ofLp (WithLp.toLp 2 F : CoarseFnL2 L 2)) = WithLp.ofLp (0 : CoarseFnL2 L 2) :=
        congrArg WithLp.ofLp h
      exact this)
  · refine AdalyFormal.Balaban.OnRangeCoercivity.range_elt_ne_zero r ?_
    intro h0
    refine hFne ?_
    have hT : r.T (r.S (WithLp.toLp 2 F : CoarseFnL2 L 2)) = WithLp.toLp 2 F :=
      r.T_S (WithLp.toLp 2 F)
    have : (WithLp.toLp 2 F : CoarseFnL2 L 2) = 0 := by
      rw [← hT]
      show r.Q (r.G (r.Qstar (r.S (WithLp.toLp 2 F : CoarseFnL2 L 2)))) = 0
      rw [h0, map_zero, map_zero, map_zero]
    exact congrArg WithLp.ofLp this

/-- `4 ∣ L μ + 1` forces the extent to carry two full coarse blocks per direction. -/
theorem coarse_wide (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) : ∀ μ : Fin 3, 2 * 2 ≤ L μ + 1 := by
  intro μ
  obtain ⟨m, hm⟩ := hdvd4 μ
  omega

/-- **THE DOOR, AT A CONCRETELY BUILT RUNG.** `OnRangeCoercivity.honestLatticeRung` inhabits the
rung type at exactly these operators, and its `hinj`/`hMpos` come from the `{QA = 0}` fibre bound —
NOT from the whole-space hypothesis `ExtentUniformCoercivity` refutes. So the one-step law on `VSrc`
is a statement about an object that is built, not merely typed. -/
theorem next_coercive_on_VSrc_at_honestRung (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {a : ℝ} (ha : 0 < a) {B : CoarseFnL2 L 2} (hB : VSrc hdvd4 (WithLp.ofLp B)) :
    gammaV / (AdalyFormal.Balaban.OnRangeCoercivity.honestLatticeRung ha
        (two_dvd_of_four hdvd4) (coarse_wide hdvd4)).q ^ 2 * ‖B‖ ^ 2
      ≤ (inner ℝ B ((AdalyFormal.Balaban.OnRangeCoercivity.honestLatticeRung ha
          (two_dvd_of_four hdvd4) (coarse_wide hdvd4)).next B) : ℝ) :=
  next_coercive_on_VSrc hdvd4 _ rfl rfl hB

end Rung

section Axioms8
#print axioms coarse_wide
#print axioms next_coercive_on_VSrc_at_honestRung
#print axioms coercive_on_VSrc_L2
#print axioms next_coercive_on_VSrc
#print axioms VSrc_carrier_nontrivial
end Axioms8

/-! ## §9 — CONTROLS: the hypothesis is LOAD-BEARING, and the domain is not degenerate

Two controls, in the two directions a prosecutor asks for.

* **MUST-FIRE / anti-vacuity** — §7's `VSrc_nontrivial` and §8's `VSrc_carrier_nontrivial`: the
  subspace carries a nonzero element, and its `H₁`-image is a nonzero fine field. So §6 and §8 are
  not statements about `{0}`.
* **MUST-NOT-FIRE / the hypothesis cannot be dropped** — `VSrc_is_load_bearing` below: at a
  site-constant lift, §6's CONCLUSION is FALSE for every positive constant (the field is nonzero and
  both quadratic forms annihilate it, `OnRangeCoercivity` §5d), and §3 shows exactly that field's
  coarse datum is what `VSrc` excludes. The two halves are proved as a conjunction so the kernel
  checks that they are about the SAME field. -/

section Controls

open AdalyFormal.Balaban.OnRangeCoercivity (siteConstCoarse suTwoLift_siteConstCoarse
  curlEnergy_siteConstLift exists_odd_site_dir)
open AdalyFormal.Balaban.FullySupplied (suTwoLift)

/-- **THE MUST-NOT-FIRE CONTROL.** The conclusion of §6 is FALSE at a nonzero site-constant lift —
so `coercive_on_VSrc_preimage` is not a theorem that would hold anyway, and §3 shows precisely that
this field's coarse datum is outside `VSrc`. Stated as a conjunction: the SAME `g` refutes the
conclusion and is excluded by the hypothesis. -/
theorem VSrc_is_load_bearing (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {g : Fin 3 → SuTwo} {ρ : Fin 3} (hg : g ρ ≠ 0) {γ : ℝ} (hγ : 0 < γ) :
    (¬ (γ * bondEnergy (suTwoLift 2 (siteConstCoarse (L := L) g))
        ≤ curlEnergy (suTwoLift 2 (siteConstCoarse (L := L) g))
          + pAx (suTwoLift 2 (siteConstCoarse (L := L) g)) (CoarseLattice L 2) 2))
      ∧ ¬ VSrc hdvd4 (siteConstCoarse (L := L) g) := by
  refine ⟨?_, siteConst_not_VSrc hdvd4 hg⟩
  intro hcon
  -- the field is nonzero
  obtain ⟨z, hz⟩ := exists_odd_site_dir (L := L) (two_dvd_of_four hdvd4) ρ
  have hval : suTwoLift 2 (siteConstCoarse (L := L) g) (z, ρ) ≠ 0 := by
    rw [suTwoLift_siteConstCoarse, if_pos (by rw [hz])]
    exact smul_ne_zero (by norm_num) hg
  have hbe : 0 < bondEnergy (suTwoLift 2 (siteConstCoarse (L := L) g)) :=
    AdalyFormal.Balaban.FibreAggregate.bondEnergy_pos _ hval
  -- both quadratic forms annihilate it
  have hcurl : curlEnergy (suTwoLift 2 (siteConstCoarse (L := L) g)) = 0 :=
    curlEnergy_siteConstLift g
  have hpax : pAx (suTwoLift 2 (siteConstCoarse (L := L) g)) (CoarseLattice L 2) 2 = 0 :=
    AdalyFormal.Balaban.ExtentUniformCoercivity.pAx_suTwoLift _
  rw [hcurl, hpax, add_zero] at hcon
  nlinarith

end Controls

section Axioms9
#print axioms VSrc_is_load_bearing
end Axioms9

section Axioms6
#print axioms pullC_eq
#print axioms coarse_fibre_bound_on_VSrc
#print axioms sum_over_blocks
#print axioms sum_shift_invariant
#print axioms coarseCurl_sq_le
#print axioms coarseCurlEnergy_Q_le
#print axioms gammaV
#print axioms gammaV_pos
#print axioms coercive_on_VSrc_preimage
end Axioms6

end AdalyFormal.Balaban.VRestrictedRoute
