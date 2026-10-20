import BalabanCompact.Class
import BalabanCompact.Group
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The quadratic form (3.156) and the headline `P428Target8`

Operators are the printed ones, written as sums and derivatives rather than as the
273-module carrier tower. Two normalisations, both recorded in the statement sheet:

* bodies are at unit spacing (`η` is restored only as the factor in front of
  `(QG₁Q*)⁻¹`);
* the matrix trace in `Δ'` and `J` is Bałaban's normalised trace `tr = ½ Tr`.

`Ring.inverse` is `0` where an operator is not invertible, so a missing inverse
makes the lower bound stronger, not weaker.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BalabanCompact

open Matrix Complex ContinuousLinearMap
open scoped Classical

variable {L : Extent}

abbrev Field (L : Extent) := PiLp 2 (fun _ : Bond L => Vec)

noncomputable def ofField (A : Field L) : Bond L → Vec := WithLp.ofLp A
noncomputable def toField (A : Bond L → Vec) : Field L := WithLp.toLp 2 A

/-! ## Paths and the one-step average, CMP98 (43), (63) -/

def coarsePathEnd (s : ℕ) : Site L → List (Fin 3) → Site L
  | y, [] => y
  | y, μ :: rest => coarsePathEnd s (coarseShift y s μ) rest

def coarseHol (s : ℕ) (V : Bond L → Matrix (Fin 2) (Fin 2) ℂ) : Site L → List (Fin 3) → Matrix (Fin 2) (Fin 2) ℂ
  | _, [] => 1
  | y, μ :: rest => V (y, μ) * coarseHol s V (coarseShift y s μ) rest

def steps (s : ℕ) (a b : Site L) (μ : Fin 3) : ℕ := ((b μ).val - (a μ).val) / s

def gammaPath (s : ℕ) (y x : Site L) : List (Fin 3) :=
  List.replicate (steps s y x 2) 2 ++
    List.replicate (steps s (Function.update y 2 (x 2)) x 1) 1 ++
      List.replicate (steps s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0) 0

def inStepBlock (y : Site L) (s ell : ℕ) (x : Site L) : Prop :=
  ∀ μ, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + s * ell ∧ s ∣ ((x μ).val - (y μ).val)

noncomputable def stepBlock (y : Site L) (s ell : ℕ) : Finset (Site L) :=
  Finset.univ.filter (inStepBlock y s ell)

def cPlus (s ell : ℕ) (c : Bond L) : Site L := coarsePathEnd s c.1 (List.replicate ell c.2)

def gammaVar (s ell : ℕ) (V : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (c : Bond L) (x : Site L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  coarseHol s V c.1 (gammaPath s c.1 x)
    * coarseHol s V x (List.replicate ell c.2)
    * (coarseHol s V (cPlus s ell c) (gammaPath s c.1 x))ᴴ

def bondVar (s ell : ℕ) (V : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (c : Bond L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  coarseHol s V c.1 (List.replicate ell c.2)

noncomputable def blocked (s ell : ℕ) (V : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (c : Bond L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  suExpM (∑ x ∈ stepBlock c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • suLogM (gammaVar s ell V c x * (bondVar s ell V c)ᴴ))
    * bondVar s ell V c

def rProdAux (s : ℕ) (V0 V1 : Bond L → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ → Site L → List (Fin 3) → Matrix (Fin 2) (Fin 2) ℂ
  | _, _, [] => 1
  | h, y, μ :: rest =>
      (h * V1 (y, μ) * hᴴ) * rProdAux s V0 V1 (h * V0 (y, μ)) (coarseShift y s μ) rest

noncomputable def sBlock (s ell : ℕ) (V0 V1 : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (y : Site L) : Vec :=
  ∑ x ∈ stepBlock y s ell, ((ell : ℝ) ^ 3)⁻¹ •
    suLogM (rProdAux s V0 V1 1 y (gammaPath s y x))

/-- CMP98 (63)/(89): `V̿_c = exp(-S₋) (V̄₁ V₀)_c exp(S₊) (V̄₀)_c⁻¹`, inverse = adjoint. -/
noncomputable def rawStep (s ell : ℕ) (V0 V1 : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (c : Bond L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  suExpM (-(sBlock s ell V0 V1 c.1))
    * blocked s ell (fun b => V1 b * V0 b) c
    * suExpM (sBlock s ell V0 V1 (cPlus s ell c))
    * (blocked s ell V0 c)ᴴ

/-- CMP98 (122), as in the frozen `qStepX`: the fluctuation is `V₁ = exp(a)`.
`rawStep` already forms `V₁ V₀` and uses `V₁` in `sBlock`, so the background is not inserted here. -/
noncomputable def qStep (s ell : ℕ) (V0 : Cfg L) (a : Bond L → Vec) : Bond L → Vec :=
  fun c => suLogM (rawStep s ell (fun b => (V0 b : Matrix _ _ ℂ)) (fun b => suExpM (a b)) c)

noncomputable def QlinStep (s ell : ℕ) (V0 : Cfg L) : (Bond L → Vec) →L[ℝ] (Bond L → Vec) :=
  ContinuousLinearMap.pi fun c => fderiv ℝ (fun a => qStep s ell V0 a c) 0

noncomputable def QlinComp (ell : ℕ) (bg : ℕ → Cfg L) : ℕ → (Bond L → Vec) →L[ℝ] (Bond L → Vec)
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (QlinStep (ell ^ j) ell (bg j)).comp (QlinComp ell bg j)

noncomputable def D2Step (s ell : ℕ) (V0 : Cfg L) (a b : Bond L → Vec) : Bond L → Vec :=
  fun c => (fderiv ℝ (fderiv ℝ (fun a => qStep s ell V0 a c)) 0 a) b

noncomputable def C2Step (s ell : ℕ) (V0 : Cfg L) (a : Bond L → Vec) : Bond L → Vec :=
  (1 / 2 : ℝ) • D2Step s ell V0 a a

/-! ## `Δ` and `J`, localised to plaquettes inside `Ω₀` -/

noncomputable def reH (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) : Matrix (Fin 2) (Fin 2) ℂ :=
  let h := let x := p.1; let μ := p.2.1.1; let ν := p.2.1.2
    U (x, μ) * U (shift x μ, ν) * (U (shift x ν, μ))ᴴ * (U (x, ν))ᴴ
  (1 / 2 : ℂ) • (h + hᴴ)

noncomputable def imH (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (p : Plaq L) : Matrix (Fin 2) (Fin 2) ℂ :=
  let h := let x := p.1; let μ := p.2.1.1; let ν := p.2.1.2
    U (x, μ) * U (shift x μ, ν) * (U (shift x ν, μ))ᴴ * (U (x, ν))ᴴ
  (1 / (2 * I) : ℂ) • (h - hᴴ)

/-- Normalised trace `tr = ½ Tr`. -/
noncomputable def ntr (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (1 / 2 : ℝ) * (M.trace).re

noncomputable def conjM (U : Matrix (Fin 2) (Fin 2) ℂ) (v : Vec) : Vec :=
  fromM (U * toM v * Uᴴ)

noncomputable def curlM (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A : Bond L → Vec) (p : Plaq L) : Vec :=
  A (p.1, p.2.1.1)
    + conjM (U (p.1, p.2.1.1)) (A (shift p.1 p.2.1.1, p.2.1.2))
    - conjM (U (p.1, p.2.1.2)) (A (shift p.1 p.2.1.2, p.2.1.1))
    - A (p.1, p.2.1.2)

/-- Diagonal of (3.10) on one plaquette: `tr (i curl)² (Re U(∂p) - 1)` plus the six commutators. -/
noncomputable def deltaPrimeAt (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A : Bond L → Vec) (p : Plaq L) : ℝ :=
  let F := toM (curlM U A p)
  let iF := I • F
  let a1 := - (U (p.1, p.2.1.2) * toM (A (shift p.1 p.2.1.2, p.2.1.1)) * (U (p.1, p.2.1.2))ᴴ)
  let a2 := - toM (A (p.1, p.2.1.2))
  let a3 := toM (A (p.1, p.2.1.1))
  let a4 := U (p.1, p.2.1.1) * toM (A (shift p.1 p.2.1.1, p.2.1.2)) * (U (p.1, p.2.1.1))ᴴ
  let Im := imH U p
  let br (X Y : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
    ntr ((I • Y) * X * Im) - ntr ((I • X) * Y * Im)
  ntr (iF * iF * (reH U p - 1)) + br a1 a2 + br a1 a3 + br a1 a4 + br a2 a3 + br a2 a4 + br a3 a4

noncomputable def gradAt (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (lam : Site L → Vec) (b : Bond L) : Vec :=
  conjM (U b) (lam (shift b.1 b.2)) - lam b.1

noncomputable def divAt (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (A : Bond L → Vec) (x : Site L) : Vec :=
  ∑ μ : Fin 3, (conjM ((U (shiftBack x μ, μ))ᴴ) (A (shiftBack x μ, μ)) - A (x, μ))

/-- Plaquette sum of `Δ'` over a plaquette set (`plaqIn Ω₀` in the lemma). Not the full `Δ`. -/
noncomputable def deltaPrimeSum (P : Set (Plaq L)) (U : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (A : Bond L → Vec) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), deltaPrimeAt U A p

end BalabanCompact
