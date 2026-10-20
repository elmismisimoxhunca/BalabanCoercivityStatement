import BalabanCompact.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Tower, region `Λ`, class of cubes, regularity (3.35)–(3.36)

The hypotheses of `P428Target8`. Names match the frozen statement
`AdalyFormal.StatementLaneG` / `StatementLane` / `StatementLane2`.
-/

set_option autoImplicit false

namespace BalabanCompact

open Matrix Complex
open scoped Classical

variable {L : Extent}

def scaleUp (ell k : ℕ) (Lu : Extent) : Extent :=
  fun μ => (Lu μ + 1) * ell ^ k - 1

structure Tower (L : Extent) where
  Om : ℕ → Set (Site L)

def bigSide (M ell j : ℕ) : ℕ := M * ell ^ j

def BlockClosed (s : ℕ) (S : Set (Site L)) : Prop :=
  ∀ x ∈ S, ∀ y : Site L, (∀ μ : Fin 3, (y μ).val / s = (x μ).val / s) → y ∈ S

/-- CMP96 (2.1)–(2.2) and the p. 396 collar for `Ω₀` (reading A: blocks of `M` fine sites). -/
def Admissible (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j, k < j → S.Om j = ∅) ∧
  (∀ j, j ≤ k → ∀ μ, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j, j ≤ k → ∀ x, x ∉ S.Om j → ∀ y ∈ S.Om (j + 1), R * bigSide M ell j < pdist x y) ∧
  (∀ x, x ∈ S.Om 0 ↔
    ∃ y ∈ S.Om 1, ∃ z : Site L,
      (∀ μ, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M)

def TorusOK (ell M : ℕ) (Lu : Extent) : Prop :=
  (∀ μ, ell ∣ Lu μ + 1) ∧ (∀ μ, ell < Lu μ + 1) ∧ (∀ μ, M ∣ Lu μ + 1)

/-- `Λ ⊂ Λ_k = Ω_k^{(k)}`, union of big blocks, distance to the complement `> RM` (p. 427). -/
def LambdaOK {Lu Lf : Extent} (ell M R k : ℕ) (S : Tower Lf) (Lam : Set (Site Lu)) : Prop :=
  BlockClosed (L := Lu) M Lam ∧
  ∃ emb : Site Lu → Site Lf,
    (∀ y μ, (emb y μ).val = ell ^ k * (y μ).val) ∧
    (∀ y ∈ Lam, emb y ∈ S.Om k) ∧
    (∀ y ∈ Lam, ∀ y' : Site Lu, emb y' ∉ S.Om k → R * M < pdist y y')

def inBlock (y : Site L) (ell : ℕ) (x : Site L) : Prop :=
  ∀ μ, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell

noncomputable def blockOf (y : Site L) (ell : ℕ) : Finset (Site L) :=
  Finset.univ.filter (inBlock y ell)

def CoarseLattice (ell : ℕ) : Set (Site L) :=
  {y | ∀ μ, (y μ).val % ell = 0}

/-- `Λ' = { y coarse | B(y) ⊂ Λ }`. -/
def LamPrime {Lu : Extent} (ell : ℕ) (Lam : Set (Site Lu)) : Set (Site Lu) :=
  {y | y ∈ CoarseLattice (L := Lu) ell ∧ ∀ x ∈ blockOf (L := Lu) y ell, x ∈ Lam}

def coarseShift (y : Site L) (ell : ℕ) (μ : Fin 3) : Site L :=
  shiftN y μ ell

/-- Staircase `Γ_{y,x}` in the order `e₃, e₂, e₁` (CMP96 p. 244). -/
noncomputable def axisSegment (base : Site L) (μ : Fin 3) (a b : ℕ) : Finset (Bond L) :=
  Finset.univ.filter fun e =>
    e.2 = μ ∧ (∀ ν, ν ≠ μ → e.1 ν = base ν) ∧ a ≤ (e.1 μ).val ∧ (e.1 μ).val < b

def corner1 (y x : Site L) : Site L := Function.update y 2 (x 2)
def corner2 (y x : Site L) : Site L := Function.update (corner1 y x) 1 (x 1)

noncomputable def staircasePath (y x : Site L) : Finset (Bond L) :=
  axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val) ∪
  axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val) ∪
  axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val) (max (y 0).val (x 0).val)

def pathSite (x : Site L) (μ : Fin 3) (i : ℕ) : Site L := shiftN x μ i

/-- Dropped bond `b₀(c) = B(c) ∩ c`, the last fine bond of the long bond. -/
def droppedBond (ell : ℕ) (c : Site L × Fin 3) : Bond L :=
  (pathSite c.1 c.2 (ell - 1), c.2)

/-- Coarse bond touching `Λ'` (at least one endpoint). -/
def CRowIn {Lu : Extent} (ell : ℕ) (Lam : Set (Site Lu)) (c : Site Lu × Fin 3) : Prop :=
  c.1 ∈ LamPrime ell Lam ∨ coarseShift (L := Lu) c.1 ell c.2 ∈ LamPrime ell Lam

def IsDroppedIn {Lu : Extent} (Lam : Set (Site Lu)) (ell : ℕ) (b : Bond Lu) : Prop :=
  ∃ c : Site Lu × Fin 3, CRowIn ell Lam c ∧ b = droppedBond (L := Lu) ell c

/-- `B̃ = 0` on staircases of `Λ'` and on dropped bonds. -/
def OnLambdaTildeIn {Lu : Extent} (Lam : Set (Site Lu)) (ell : ℕ) (B : Bond Lu → Vec) : Prop :=
  (∀ y ∈ LamPrime ell Lam, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0) ∧
  (∀ b, IsDroppedIn Lam ell b → B b = 0)

/-- Touching support: `B̃(b) = 0` unless some endpoint lies in `Λ`. -/
def OnLambdaT {Lu : Extent} (Lam : Set (Site Lu)) (B : Bond Lu → Vec) : Prop :=
  ∀ b, ¬ (b.1 ∈ Lam ∨ shift b.1 b.2 ∈ Lam) → B b = 0

def towerBj (S : Tower L) (j : ℕ) : Set (Site L) := S.Om j \ S.Om (j + 1)

def siteBox (z : Site L) (s : ℕ) : Set (Site L) :=
  {x | ∀ μ, ((x μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < s}

def GridCorner (s : ℕ) (z : Site L) : Prop := ∀ μ, (z μ).val % s = 0

def DescribedAt (ell M f k : ℕ) (S : Tower L) (sites : Set (Site L)) (i : ℕ) : Prop :=
  i ≤ k ∧
  (∃ z, GridCorner (bigSide M ell i) z ∧ sites = siteBox z (f * bigSide M ell i)) ∧
  sites ⊆ towerBj S i ∪ towerBj S (i + 1) ∧
  (sites ∩ towerBj S i).Nonempty

def IsClassCube (ell M f k : ℕ) (S : Tower L) (sites : Set (Site L)) (j : ℕ) : Prop :=
  DescribedAt ell M f k S sites j ∧ ∀ i, DescribedAt ell M f k S sites i → i = j

/-- Both endpoints in the cube (the frozen reading of class bonds). -/
def CubeBond (sites : Set (Site L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∧ shift b.1 b.2 ∈ sites

noncomputable def frobSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (M 0 0) + Complex.normSq (M 0 1) + Complex.normSq (M 1 0) + Complex.normSq (M 1 1)

noncomputable def frobNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (frobSq M)

/-- Hermitian and traceless: the printed chart `U = exp(i η A)`. -/
def HT (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Xᴴ = X ∧ X.trace = 0

noncomputable def curlA (η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (x : Site L) (a b : Fin 3) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (η⁻¹ : ℝ) • (A (shift x a, b) - A (x, b) - A (shift x b, a) + A (x, a))

def CurlReads (sites : Set (Site L)) (x : Site L) (a b : Fin 3) : Prop :=
  CubeBond sites (shift x a, b) ∧ CubeBond sites (x, b) ∧
  CubeBond sites (shift x b, a) ∧ CubeBond sites (x, a)

noncomputable def ddA (η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (x : Site L) (μ : Fin 3) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (η⁻¹ : ℝ) • ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
    (curlA η A (shiftBack x ν) ν μ - curlA η A x ν μ)

/-- (3.35)+(3.36), curl form of `∂*∂`, one cube factor `f`, gauge existential inside the cube. -/
def PerCubeRegular (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : Cfg L) : Prop :=
  ∀ sites j, IsClassCube ell M f k S sites j →
    ∃ (g : Site L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e, CubeBond sites e →
        HT (A e) ∧
        ((gauge g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * ((ell : ℝ) ^ j * η)⁻¹) ∧
      (∀ μ ν x, CubeBond sites (x, ν) → CubeBond sites (shift x μ, ν) →
        frobNorm ((η⁻¹ : ℝ) • (A (shift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ μ x, (∀ ν, ν ≠ μ → CurlReads sites (shiftBack x ν) ν μ ∧ CurlReads sites x ν μ) →
        frobNorm (ddA η A x μ) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

def plaqIn (S : Set (Site L)) : Set (Plaq L) :=
  {p | ∀ e ∈ boundary p, e.1 ∈ S ∧ shift e.1 e.2 ∈ S}

def CoversOm0c (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ sites j, IsClassCube ell M c k S sites j ∧ x ∈ sites

def CoversPlaqOm0c (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p, (∀ e ∈ boundary p, CubeBond (S.Om 0) e) →
    ∃ sites j, IsClassCube ell M c k S sites j ∧ ∀ e ∈ boundary p, CubeBond sites e

def CoversOm0p (ell M c k : ℕ) (S : Tower L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqOm0c ell M c k S

/-- One cube factor for coverage and for (3.35)–(3.36). -/
def ClassCoupled (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : Cfg L) : Prop :=
  CoversOm0p ell M c k S ∧ PerCubeRegular ell M c k S α₀ η U

/-- `Λ = B(Λ')`. -/
def LamBlockSum {Lu : Extent} (ell : ℕ) (Lam : Set (Site Lu)) : Prop :=
  ∀ x ∈ Lam, ∃ y ∈ LamPrime ell Lam, x ∈ blockOf (L := Lu) y ell

def LambdaOK2 {Lu Lf : Extent} (ell M R k : ℕ) (S : Tower Lf) (Lam : Set (Site Lu)) : Prop :=
  LambdaOK ell M R k S Lam ∧ LamBlockSum ell Lam

/-- `‖B̃‖² = ∑_b ‖B̃(b)‖²`, trace-normalised Hilbert–Schmidt norm via the Pauli basis. -/
noncomputable def bondEnergy {Lu : Extent} (B : Bond Lu → Vec) : ℝ :=
  ∑ b : Bond Lu, ‖B b‖ ^ 2

end BalabanCompact
