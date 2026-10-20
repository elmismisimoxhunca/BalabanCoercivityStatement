import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Lattice, SU(2) and the trace-normalised norm

Dimension 3. Sites of a torus of extent `L` are `(μ : Fin 3) → Fin (L μ + 1)`
(the stored integer is one less than the number of sites). Bonds are oriented
coordinate edges. `𝔰𝔲(2)` is identified with `ℝ³` by the orthonormal basis

* `E₀ = i σ₁ = [[0, i], [i, 0]]`
* `E₁ = i σ₂ = [[0, 1], [-1, 0]]`
* `E₂ = i σ₃ = [[i, 0], [0, -i]]`

which is orthonormal for Bałaban's product `⟨X, Y⟩ = -½ Tr(XY)` (CMP99b p. 392:
`tr 1 = 1`). The Euclidean norm on coordinates is therefore the printed
Hilbert–Schmidt norm.
-/

set_option autoImplicit false

namespace BalabanCompact

open Matrix Complex

abbrev Extent := Fin 3 → ℕ
abbrev Site (L : Extent) := (μ : Fin 3) → Fin (L μ + 1)
abbrev Bond (L : Extent) := Site L × Fin 3
abbrev PlaqDir := {d : Fin 3 × Fin 3 // d.1 < d.2}
abbrev Plaq (L : Extent) := Site L × PlaqDir

def shift {L : Extent} (x : Site L) (μ : Fin 3) : Site L :=
  Function.update x μ (x μ + 1)

def shiftBack {L : Extent} (x : Site L) (μ : Fin 3) : Site L :=
  Function.update x μ (x μ - 1)

def shiftN {L : Extent} (x : Site L) (μ : Fin 3) : ℕ → Site L
  | 0 => x
  | n + 1 => shift (shiftN x μ n) μ

/-- Periodic `ℓ¹` distance (CMP96 p. 223), shortest way round each circle. -/
def pcd (N a b : ℕ) : ℕ :=
  min (if a ≤ b then b - a else a - b) (N - (if a ≤ b then b - a else a - b))

def pdist {L : Extent} (x y : Site L) : ℕ :=
  ∑ μ : Fin 3, pcd (L μ + 1) (x μ).val (y μ).val

/-! ## `𝔰𝔲(2) ≅ ℝ³` -/

abbrev Vec := EuclideanSpace ℝ (Fin 3)

def Emat : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, I; I, 0]
  | 1 => !![0, 1; -1, 0]
  | 2 => !![I, 0; 0, -I]

noncomputable def toM (v : Vec) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 3, (v i) • Emat i

/-- Coordinates dual to `Emat`. -/
noncomputable def fromM (X : Matrix (Fin 2) (Fin 2) ℂ) : Vec :=
  WithLp.toLp 2 fun i =>
    match i with
    | 0 => (X 0 1).im
    | 1 => (X 0 1).re
    | 2 => (-I * X 0 0).re

/-! ## Closed-form exponential, the restriction of `exp` to this basis -/

/-- `exp(toM v) = cos r · 1 + sinc r · toM v`, with `r = ‖v‖`. -/
noncomputable def suExpM (v : Vec) : Matrix (Fin 2) (Fin 2) ℂ :=
  Real.cos ‖v‖ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.sinc ‖v‖ • toM v

/-! ## Logarithm on `SU(2)`, principal branch, value `0` at `-1` -/

/-- `θ = arccos(Re(tr U)/2) ∈ [0, π]`. -/
noncomputable def suAngle (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  Real.arccos (((U : Matrix (Fin 2) (Fin 2) ℂ).trace / 2).re)

/-- Principal logarithm in coordinates. At `±I` the formula is the limit `0`
when `U = 1`; at `U = -1` the logarithm is not unique and the value is `0`
(the same junk convention as a logarithm undefined on the cut). -/
noncomputable def suLog (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Vec :=
  let θ := suAngle U
  let S := (U : Matrix (Fin 2) (Fin 2) ℂ) - Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  if θ = 0 ∨ Real.sin θ = 0 then 0 else (θ / Real.sin θ) • fromM S

/-- The same formula on a raw matrix (used for the averaging chart). -/
noncomputable def suLogM (U : Matrix (Fin 2) (Fin 2) ℂ) : Vec :=
  let θ := Real.arccos ((U.trace / 2).re)
  let S := U - Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  if θ = 0 ∨ Real.sin θ = 0 then 0 else (θ / Real.sin θ) • fromM S

/-! ## Link configurations -/

abbrev Cfg (L : Extent) := Bond L → Matrix.specialUnitaryGroup (Fin 2) ℂ

def gauge {L : Extent} (γ : Site L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (U : Cfg L) : Cfg L :=
  fun e => γ e.1 * U e * (γ (shift e.1 e.2))⁻¹

def holonomy {L : Extent} (U : Cfg L) (p : Plaq L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  let x := p.1; let μ := p.2.1.1; let ν := p.2.1.2
  U (x, μ) * U (shift x μ, ν) * (U (shift x ν, μ))⁻¹ * (U (x, ν))⁻¹

def boundary {L : Extent} (p : Plaq L) : Finset (Bond L) :=
  let x := p.1; let μ := p.2.1.1; let ν := p.2.1.2
  {(x, μ), (shift x μ, ν), (shift x ν, μ), (x, ν)}

/-- `Re U(∂p) = ½ (U(∂p) + U(∂p)⁻¹)`. -/
noncomputable def reHol {L : Extent} (U : Cfg L) (p : Plaq L) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • ((holonomy U p : Matrix _ _ ℂ) + ((holonomy U p)⁻¹ : Matrix _ _ ℂ))

/-- `Im U(∂p) = (1/(2i)) (U(∂p) - U(∂p)⁻¹)`. -/
noncomputable def imHol {L : Extent} (U : Cfg L) (p : Plaq L) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (2 * I) : ℂ) • ((holonomy U p : Matrix _ _ ℂ) - ((holonomy U p)⁻¹ : Matrix _ _ ℂ))

/-- Conjugation `R(U) X = U X U⁻¹` on coordinates. -/
noncomputable def Rmap (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Vec) : Vec :=
  fromM ((U : Matrix _ _ ℂ) * toM v * (U : Matrix _ _ ℂ)⁻¹)

/-- Covariant derivative `(D_U λ)(b) = R(U(b)) λ(b₊) - λ(b₋)` (CMP99b (3.3)). -/
noncomputable def gradValue {L : Extent} (U : Cfg L) (lam : Site L → Vec) (b : Bond L) : Vec :=
  Rmap (U b) (lam (shift b.1 b.2)) - lam b.1

/-- Covariant curl (CMP99b (3.4)). -/
noncomputable def curlValue {L : Extent} (U : Cfg L) (A : Bond L → Vec) (p : Plaq L) : Vec :=
  A (p.1, p.2.1.1)
    + Rmap (U (p.1, p.2.1.1)) (A (shift p.1 p.2.1.1, p.2.1.2))
    - Rmap (U (p.1, p.2.1.2)) (A (shift p.1 p.2.1.2, p.2.1.1))
    - A (p.1, p.2.1.2)

end BalabanCompact
