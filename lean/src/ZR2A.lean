import ZNonVacuity2

/-!
# R2A -- statement lane r2, part A: repaired class / coverage / variants (CMP99b p.396, p.427, p.428)
No sorry / native_decide / axioms.  Nothing here proves the lemma.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.StatementLane

/-! ## D3 (Opus prosecution): (3.36) is `|∂^{η*}∂^η A|` with `∂` the EXTERIOR derivative
(p.392 (3.8),(3.9): `D*D` "generalizing ∂*∂"), not the componentwise vector Laplacian that r1 used
(= δd + dδ).  Here: `curlA` = `(∂^η A)` on the plaquette `(x; a, b)`, i.e. the discrete curl
`η⁻¹ (A_b(x+a) − A_b(x) − A_a(x+b) + A_a(x))`, and `ddA` = `(∂^{η*} ∂^η A)_μ(x)` =
`Σ_{ν≠μ} η⁻¹ (F_{νμ}(x−ν) − F_{νμ}(x))` by (3.9) with (3.8) at `R(U)=1`.  The two classes are
NOT claimed equal. -/

open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

noncomputable def curlA {L : PeriodicLatticeExtent} (η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (η⁻¹ : ℝ) • (A (periodicLatticeShift x a, b) - A (x, b)
    - A (periodicLatticeShift x b, a) + A (x, a))

/-- the four bonds the plaquette `(x;a,b)` reads lie in the cube -/
def CurlReads {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  CubeBond sites (periodicLatticeShift x a, b) ∧ CubeBond sites (x, b) ∧
  CubeBond sites (periodicLatticeShift x b, a) ∧ CubeBond sites (x, a)

noncomputable def ddA {L : PeriodicLatticeExtent} (η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (η⁻¹ : ℝ) • ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
    (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ)

/-- **(3.35)+(3.36), curl form.**  Same quantifier structure as r1 `PerCubeRegular`
(`∃ g A` inside `∀ cube`); only clause 3 changes. -/
def PerCubeRegular2 {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, CubeBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        CubeBond sites ((x, ν) : Bond L) → CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReads sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

theorem perCubeRegular2_gauge {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (h : PerCubeRegular2 ell M f k S α₀ η U)
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PerCubeRegular2 ell M f k S α₀ η (periodicGaugeTransform γ U) := by
  intro sites j hq
  obtain ⟨g, A, hA, hD, hLap⟩ := h sites j hq
  refine ⟨fun x => g x * (γ x)⁻¹, A, ?_, hD, hLap⟩
  intro e he
  obtain ⟨h1, h2, h3⟩ := hA e he
  refine ⟨h1, ?_, h3⟩
  have hg : periodicGaugeTransform (fun x => g x * (γ x)⁻¹) (periodicGaugeTransform γ U) e
      = periodicGaugeTransform g U e := by
    unfold periodicGaugeTransform
    group
  rw [hg]
  exact h2

/-! ## D4: per-cube factor.  The print: "Here O(1) will mean a number >= 10" attached to EACH cube.
`PerCubeRegularMix F` = every class cube of every size f in [10,F] is regular with that cube's own f. -/

def PerCubeRegularMix {L : PeriodicLatticeExtent} (ell M F k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ f : ℕ, 10 ≤ f → f ≤ F → PerCubeRegular2 ell M f k S α₀ η U

theorem PerCubeRegularMix.toClass {L : PeriodicLatticeExtent} {ell M F k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (h : PerCubeRegularMix ell M F k S α₀ η U) {f : ℕ}
    (h1 : 10 ≤ f) (h2 : f ≤ F) : PerCubeRegular2 ell M f k S α₀ η U := h f h1 h2

/-! ## D2: coverage.  p.396: the regularity conditions "do not impose any constraints on U outside
the domain Omega_0" -- i.e. they ARE imposed on all of Omega_0.  A site of Omega_0 not inside any
class cube is a site the class fails to constrain; Sthin (r1 prosecution) is exactly that. -/

/-- every site of `Ω₀` lies in a class cube (of some size `f ∈ [10,F]`). -/
def CoversOm0 {L : PeriodicLatticeExtent} (ell M F k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j f : ℕ),
    10 ≤ f ∧ f ≤ F ∧ IsClassCube ell M f k S sites j ∧ x ∈ sites

/-- **r5 (4)**: coverage with ONE fixed cube factor `c` (the print's single `O(1)`; headline `c = 12`, CMP99b p.409):
every site of `Ω₀` lies in a class cube of factor exactly `c`. -/
def CoversOm0c {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
    IsClassCube ell M c k S sites j ∧ x ∈ sites

/-- a fixed-factor cover is a range cover (`10 ≤ c ≤ F`). -/
theorem CoversOm0c.toRange {L : PeriodicLatticeExtent} {ell M c k F : ℕ} {S : Tower L}
    (h : CoversOm0c ell M c k S) (h1 : 10 ≤ c) (h2 : c ≤ F) : CoversOm0 ell M F k S := by
  intro x hx
  obtain ⟨sites, j, hc, hxs⟩ := h x hx
  exact ⟨sites, j, c, h1, h2, hc, hxs⟩

/-! ## Touching bond convention (CMP96 p.245 before Lemma 2.4: "a set of bonds b such that at least
one of the end-points b_-, b_+ belongs to Lambda"). r1's `OnLambda` required BOTH endpoints. -/

def OnLambdaT {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu))
    (B : Bond Lu → SuTwo) : Prop :=
  ∀ b : Bond Lu, ¬ (b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) → B b = 0

theorem OnLambda.toT {Lu : PeriodicLatticeExtent} {Lam : Set (PeriodicLatticeSite Lu)}
    {B : Bond Lu → SuTwo} (h : OnLambda Lam B) : OnLambdaT Lam B := by
  intro b hb
  exact h b (fun hh => hb (Or.inl hh.1))

/-! ## The claim at fixed (k, Lu, Lf) with the repaired hypotheses -/

/-- `CoercAt` repaired: (i) per-cube factors up to the cap `F` (`PerCubeRegularMix F`, curl form),
(ii) coverage of Omega_0, (iii) touching bond set for `B̃`. -/
def CoercAt2 (ell M R k : ℕ) {Lu Lf : PeriodicLatticeExtent} (I : IngrFam ell Lu Lf)
    (F : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower Lf), Admissible ell M R k S → CoversOm0 ell M F k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK ell M R k S Lam →
  ∀ (U : LinkCfg Lf), PerCubeRegularMix ell M F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤ (I S U Lam).form (WithLp.toLp 2 ((I S U Lam).C Bt))

/-- The cube-size cap `F` (the print's fixed `O(1) ≥ 10`) and `R` are STATEMENT PARAMETERS fixed
before `a₀, γ₀`; `R ≥ F + 2` replaces r1's `0 < R`.  (This alone does NOT make the class
non-empty on every admissible tower: for `k = 0` `Admissible` does not constrain `Ω₀` at all;
`CoversOm0` is therefore a hypothesis on the tower, and `Sthin` shows it cannot be dropped.) -/
def P428Strong (ell M R F : ℕ) (I : IngrFamK ell) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * M * α₀ ≤ a₀ →
      CoercAt2 ell M R k (I k Lu) F α₀ γ₀

/-- Printed reading: p.428 says only "γ₀ > 0 independent of k and U": γ₀ may depend on the torus. -/
def P428Print (ell M R F : ℕ) (I : IngrFamK ell) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ (Lu : PeriodicLatticeExtent),
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (k : ℕ) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * M * α₀ ≤ a₀ →
      CoercAt2 ell M R k (I k Lu) F α₀ γ₀

theorem P428Strong.toPrint {ell M R F : ℕ} {I : IngrFamK ell} (h : P428Strong ell M R F I) :
    P428Print ell M R F I := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, fun Lu => ⟨γ₀, hγ, fun k α₀ h1 h2 => h k Lu α₀ h1 h2⟩⟩

#print axioms CoversOm0c.toRange
#print axioms perCubeRegular2_gauge
#print axioms P428Strong.toPrint

end AdalyFormal.StatementLane2
