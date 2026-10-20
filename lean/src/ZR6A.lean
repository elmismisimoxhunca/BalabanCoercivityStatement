import ZR2A

/-!
# ZR6A -- r6 (R2): PLAQUETTE coverage of `Ω₀` by class cubes  [statement lane r6]

CMP99b p.396 (page image, verbatim): "these regularity conditions do not impose any constraints on U outside the
domain Ω₀."  The class constrains `U` only on the bonds of the class cubes (`CubeBond`).  With the operators
localised to the plaquettes `plaqIn Ω₀` (`ZLocOps`; the lane's reading of p.394, not the printed wording), every plaquette of `Ω₀` must have its four
boundary bonds among the class-constrained bonds, i.e. `CoversPlaqOm0c`: each plaquette of `Ω₀` has all four boundary
bonds `CubeBond`s of ONE class cube.  (`CoversOm0c`, r5, covers SITES only; a plaquette `p ⊂ Ω₀` whose corners lie in
different cubes has an unconstrained holonomy -- the r5-Opus R2 remark.)
`CoversOm0p := CoversOm0c ∧ CoversPlaqOm0c` is the r6 coverage hypothesis.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban

/-- every plaquette of `Ω₀` (all four boundary bonds have both endpoints in `Ω₀`) has all four boundary bonds
inside one class cube. -/
def CoversPlaqOm0c {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e

/-- r6 coverage: sites (r5) AND plaquettes. -/
def CoversOm0p {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqOm0c ell M c k S

theorem CoversOm0p.sites {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L}
    (h : CoversOm0p ell M c k S) : CoversOm0c ell M c k S := h.1

theorem CoversOm0p.plaq {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L}
    (h : CoversOm0p ell M c k S) : CoversPlaqOm0c ell M c k S := h.2

/-- a class cube containing EVERY site covers every plaquette. -/
theorem CoversPlaqOm0c_of_universal_cube {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L}
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) (hc : IsClassCube ell M c k S sites j)
    (hall : ∀ x, x ∈ sites) : CoversPlaqOm0c ell M c k S :=
  fun _ _ => ⟨sites, j, hc, fun e _ => ⟨hall _, hall _⟩⟩

/-- if a cube containing every site exists, site coverage (of `Ω₀`) and plaquette coverage both hold. -/
theorem CoversOm0p_of_universal_cube {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L}
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) (hc : IsClassCube ell M c k S sites j)
    (hall : ∀ x, x ∈ sites) : CoversOm0p ell M c k S :=
  ⟨fun x _ => ⟨sites, j, hc, hall x⟩, CoversPlaqOm0c_of_universal_cube sites j hc hall⟩

/-- the constant tower `Sk` (`Ω_j = ` torus, `j ≤ k`): ONE class cube (a box of side `c · M · ell^k` anchored at the
origin, `≥` the torus) contains every site, so the r6 coverage (sites and plaquettes) holds. -/
theorem SkG_coversp {L : PeriodicLatticeExtent} (ell M k c : ℕ) (hell : 0 < ell) (hM : 0 < M) (hc : 0 < c)
    (hle : ∀ μ : Fin 3, L μ + 1 ≤ c * (M * ell ^ k)) :
    CoversOm0p ell M c k (Sk L k) := by
  have hsz : 0 < c * bigSide M ell k := by
    simp only [bigSide]; exact Nat.mul_pos hc (Nat.mul_pos hM (pow_pos hell k))
  have hB : ∀ i, i < k → towerBj (Sk L k) i = ∅ := by
    intro i hi
    have h1 : i ≤ k := by omega
    have h2 : i + 1 ≤ k := by omega
    ext y
    simp [towerBj, Sk, h1, h2]
  have hBk : towerBj (Sk L k) k = Set.univ := by
    ext y
    simp [towerBj, Sk]
  have hnon : (siteBox (L := L) (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide M ell k)
      ∩ towerBj (Sk L k) k).Nonempty := by
    refine ⟨fun μ => ⟨0, Nat.succ_pos _⟩, ?_, by rw [hBk]; exact Set.mem_univ _⟩
    intro μ
    simpa using hsz
  have hall : ∀ x : PeriodicLatticeSite L,
      x ∈ siteBox (L := L) (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide M ell k) := by
    intro x μ
    have h1 := (x μ).isLt
    have h2 := hle μ
    have : ((x μ).val + (L μ + 1) - 0) % (L μ + 1) = (x μ).val := by
      rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
    simp only [bigSide, this]
    exact lt_of_lt_of_le h1 h2
  have hcube : IsClassCube ell M c k (Sk L k)
      (siteBox (L := L) (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide M ell k)) k := by
    refine ⟨⟨le_refl k, ⟨_, ?_, rfl⟩, ?_, hnon⟩, ?_⟩
    · intro μ; simp
    · intro y _; left; rw [hBk]; exact Set.mem_univ _
    · intro i hi
      by_contra hne
      have hlt : i < k := lt_of_le_of_ne hi.1 hne
      obtain ⟨y, _, hy⟩ := hi.2.2.2
      rw [hB i hlt] at hy
      exact hy
  exact CoversOm0p_of_universal_cube _ k hcube hall

#print axioms SkG_coversp

#print axioms CoversPlaqOm0c_of_universal_cube
#print axioms CoversOm0p_of_universal_cube

/-- **R2 pin (content).**  With plaquette coverage, every plaquette of `Ω₀` has all four boundary bonds gauge-trivialised BY ONE
gauge transformation `g` (the cube's) into `exp(iηA)` with `A` Hermitian-traceless and small: the class controls the plaquette
holonomy.  (Without plaquette coverage the four bonds may lie in different cubes with different gauges; a mutant weakening
`CoversPlaqOm0c` to a one-corner condition cannot prove this.) -/
theorem plaq_common_gauge {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hcov : CoversPlaqOm0c ell M f k S) (hU : PerCubeRegular2 ell M f k S α₀ η U)
    (p : PeriodicLatticePlaquette L) (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) :
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ),
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        RMapLipschitz.frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1) := by
  obtain ⟨sites, j, hq, hcb⟩ := hcov p hp
  obtain ⟨g, A, hA, -, -⟩ := hU sites j hq
  exact ⟨g, A, j, fun e he => hA e (hcb e he)⟩

#print axioms plaq_common_gauge

/-- **r7 (F2): the class cube factor and the coverage cube factor are ONE binder `c`.**  `ClassCoupled ell M c k S α₀ η U` is the conjunction
`CoversOm0p ell M c k S ∧ PerCubeRegular2 ell M c k S α₀ η U` with the SAME `c` in both conjuncts; it is the single regularity hypothesis of
`CoercG8At` (ZT5A).  (The r6 statement had the two as separate hypotheses, so a decoupled `c`/`c+1` mutant compiled through every consumer:
`statement_audit_r6_opus` N2d.) -/
def ClassCoupled {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ PerCubeRegular2 ell M c k S α₀ η U

/-- the content the coupling buys, at one plaquette `p`: its four boundary bonds are gauge-trivialised BY ONE `g` into `exp(iηA)`, `A` Hermitian-traceless,
`‖A(e)‖ < c · M · α₀ · (ell^j η)⁻¹`. -/
def PlaqGaugeAt {L : PeriodicLatticeExtent} (ell M c : ℕ) (α₀ η : ℝ) (U : LinkCfg L) (p : PeriodicLatticePlaquette L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ),
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        RMapLipschitz.frobNorm (A e) < (c : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)

/-- **COUPLING THEOREM (F2).**  From the single hypothesis `ClassCoupled .. c ..` (same `c` for coverage and class), every plaquette whose four bonds lie in `Ω₀` is
gauge-trivialised by one `g` with the class bound at factor `c`.  This is `plaq_common_gauge`, whose proof needs the coverage factor and the class factor to be
the SAME `c` (a `c`/`c+1` split does not type-check: `CoversPlaqOm0c .. c ..` against `PerCubeRegular2 .. (c+1) ..`). -/
theorem ClassCoupled.plaq_gauge {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U)
    (p : PeriodicLatticePlaquette L) (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) :
    PlaqGaugeAt ell M c α₀ η U p :=
  plaq_common_gauge h.1.2 h.2 p hp

theorem ClassCoupled.covers {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U) : CoversOm0p ell M c k S := h.1

theorem ClassCoupled.regular {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U) : PerCubeRegular2 ell M c k S α₀ η U := h.2

#print axioms ClassCoupled.plaq_gauge

end AdalyFormal.StatementLane2
