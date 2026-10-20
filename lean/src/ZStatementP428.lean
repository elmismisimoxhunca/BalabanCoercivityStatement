import AdalyFormal.Balaban.CoercUMainDesigned
import AdalyFormal.Balaban.RMapLipschitz
import AdalyFormal.Balaban.CoarseCurl

/-!
# StatementP428 -- a restatement of CMP99b p.428 `C*Δ_kC ≥ γ₀` (STATEMENT LANE, 2026-10-09)

NOTHING HERE IS A PROOF OF THE LEMMA.  This file defines the statement, with every quantifier and
every hypothesis of the print explicit, and proves structural/non-vacuity facts about it.
No `sorry`, no `native_decide`, no new axioms.

Sources (corpus/pages, `verification_status: adjudicated`):
  p.396  (3.35),(3.36): per-cube `∃ u` gauge, `U^u = e^{iηA}`, bounds `O(1) M α₀ (L^j η)^{-1,-2,-3}`.
  p.393  `Ω₀ ⊃ … ⊃ Ω_k`, `Ω_j ⊂ T_η`, `Ω_j \ Ω_{j+1} = B^j(Λ_j)`, `Ω_{k+1} = ∅`.
  p.427  (3.155): `Λ ⊂ Λ_k = Ω_k^{(k)}`, `Λ` union of big blocks, distance to `Λ_k^c` > `RM`;
         operators "defined by the sequence {Ω_j} and a configuration U satisfying (3.35),(3.36)".
  p.428  (3.156): `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩` on
         `{B=0 on Λᶜ, B=0 on ∪Ax(y), Q₁B=0}`, `B = C B̃`; then
         "positive definite operator C*Δ_kC with a lower bound γ₀>0 independent of k and U ...
          arbitrary configuration U satisfying (3.35),(3.36) with Mα₀ sufficiently small".
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.FullReparamC (IsDropped)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg OnLambdaTilde)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-! ## §1 -- geometry of the tower (p.393, p.396) -/

/-- The fine torus carrying `Ω_j ⊂ T_η` and `U`, over the unit torus carrying `B`: extents store
`N-1`, so the unit torus with `N_u` sites per direction has `N_u · ell^k` fine sites. -/
def scaleUp (ell k : ℕ) (Lu : PeriodicLatticeExtent) : PeriodicLatticeExtent :=
  fun μ => (Lu μ + 1) * ell ^ k - 1

/-- Raw domain data `{Ω_j}_{j ≥ 0}` on the fine torus. The height `k` is NOT a field; it is the
explicit parameter of `Admissible` (p.393: `Ω_{k+1} = ∅`). -/
structure Tower (L : PeriodicLatticeExtent) where
  Om : ℕ → Set (PeriodicLatticeSite L)

/-- Side (in fine sites) of a level-`j` big block: `M · ell^j`. -/
def bigSide (M ell j : ℕ) : ℕ := M * ell ^ j

/-- `S` is a union of axis-aligned blocks of side `s` (blocks cut at multiples of `s`). -/
def BlockClosed {L : PeriodicLatticeExtent} (s : ℕ) (S : Set (PeriodicLatticeSite L)) : Prop :=
  ∀ x ∈ S, ∀ y : PeriodicLatticeSite L, (∀ μ : Fin 3, (y μ).val / s = (x μ).val / s) → y ∈ S

/-- Periodic distance on `ℤ/N`. -/
def pcd (N a b : ℕ) : ℕ :=
  min (if a ≤ b then b - a else a - b) (N - (if a ≤ b then b - a else a - b))

/-- **r5 (1)**: the `ℓ¹` periodic distance, `|x - y| = Σ_μ |x_μ - y_μ|` with each coordinate difference taken in
the shortest circular representative on `ℤ/N_μ`.  CMP96 p.223 (image): "a distance between two points
x, y ∈ ηZ^d, η > 0, is given by the l¹-norm of the vector x − y and is denoted by |x−y|, i.e.
|x−y| = Σ_{μ=1}^d |x_μ − y_μ|".  (The circular wrap is NOT printed; it is the torus reading of the print's `|x_μ − y_μ|`.)
r2..r4 used `Finset.univ.sup` (ℓ^∞). -/
def pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) : ℕ :=
  ∑ μ : Fin 3, pcd (L μ + 1) (x μ).val (y μ).val

/-- The tower conditions of CMP96 (2.1)-(2.4) as the percube lane transcribed them, plus the CMP99b base law for
`Ω₀` (p.396: "Λ₀ = Ω₀\Ω₁, where Ω₀ = {a union of big blocks of the lattice T₁, such that their distances to Ω₁ are
≤ RM}").  **r5 (2)**: the last conjunct is NO LONGER guarded by `1 ≤ k`: at `k = 0`, `Ω₁ = ∅` forces `Ω₀ = ∅`
(`admissible_k0_om0_empty`), the printed reading; r2..r4 left `Ω₀` free at `k = 0`. -/
def Admissible {L : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j : ℕ, j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
      ∀ y ∈ S.Om (j + 1), R * bigSide M ell j < pdist x y) ∧
  (∀ x : PeriodicLatticeSite L, x ∈ S.Om 0 ↔
      ∃ y ∈ S.Om 1, ∃ z : PeriodicLatticeSite L,
        (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M)

/-- general form: at `k = 0` admissibility empties `Ω₀` (r5 (2); false under the r2..r4 guarded definition). -/
theorem admissible_k0_om0_empty {L : PeriodicLatticeExtent} {ell M R : ℕ} {S : Tower L}
    (h : Admissible ell M R 0 S) : S.Om 0 = ∅ := by
  obtain ⟨-, hv, -, -, -, hc⟩ := h
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, -⟩ := (hc x).mp hx
    rw [hv 1 (by omega)] at hy
    exact hy
  · intro hx; exact hx.elim

/-- r5 (1) control: a test torus (10 sites per direction) and two sites at `ℓ¹`-distance `3` but `ℓ^∞`-distance `1`. -/
def Ltest : PeriodicLatticeExtent := fun _ => 9

theorem pdist_l1_diag :
    pdist (L := Ltest) (fun _ => 0) (fun _ => 1) = 3 := by
  unfold pdist pcd Ltest
  decide

theorem sup_pdist_diag :
    Finset.univ.sup (fun μ : Fin 3 => pcd (Ltest μ + 1) ((fun _ => (0 : Fin 10)) μ).val ((fun _ => (1 : Fin 10)) μ).val) = 1 := by
  unfold pcd Ltest
  decide

/-- `ℓ¹` dominates `ℓ^∞` -/
theorem sup_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    Finset.univ.sup (fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val) ≤ pdist x y := by
  unfold pdist
  refine Finset.sup_le (fun μ _ => ?_)
  exact Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)

/-- `B^j(Λ_j) = Ω_j \ Ω_{j+1}`. -/
def towerBj {L : PeriodicLatticeExtent} (S : Tower L) (j : ℕ) : Set (PeriodicLatticeSite L) :=
  S.Om j \ S.Om (j + 1)

/-- Periodic axis-aligned box of side `s` with corner `z`. -/
def siteBox {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) (s : ℕ) :
    Set (PeriodicLatticeSite L) :=
  {x | ∀ μ : Fin 3, ((x μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < s}

def GridCorner {L : PeriodicLatticeExtent} (s : ℕ) (z : PeriodicLatticeSite L) : Prop :=
  ∀ μ : Fin 3, (z μ).val % s = 0

/-- p.396: a cube "with index `i`": `□ ⊂ B^i(Λ_i) ∪ B^{i+1}(Λ_{i+1})`, `□ ∩ B^i(Λ_i) ≠ ∅`, and
`□` is a union of big blocks of level `i` with side `O(1) M L^i` (here `O(1) = f`). -/
def DescribedAt {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (i : ℕ) : Prop :=
  i ≤ k ∧
  (∃ z : PeriodicLatticeSite L, GridCorner (bigSide M ell i) z ∧
      sites = siteBox z (f * bigSide M ell i)) ∧
  sites ⊆ towerBj S i ∪ towerBj S (i + 1) ∧
  (sites ∩ towerBj S i).Nonempty

/-- "For each cube of this class there exists a UNIQUE index `j`". -/
def IsClassCube {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  DescribedAt ell M f k S sites j ∧ ∀ i : ℕ, DescribedAt ell M f k S sites i → i = j

/-- The bonds "of the cube": both endpoints in the cube. -/
def CubeBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∧ periodicLatticeShift b.1 b.2 ∈ sites

/-! ## §2 -- (3.35),(3.36): the per-cube regularity class -/

/-- Hermitian traceless: `A ∈ 𝔰𝔲(2)` in the physicists' convention `U = e^{iηA}`. -/
def HT (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop := X.conjTranspose = X ∧ Matrix.trace X = 0

/-- **(3.35)+(3.36)**, literally: for EVERY class cube □ (index `j`) THERE EXISTS a gauge
transformation on □ (`∃ g` INSIDE the `∀ □`) and `A` with `U^g = e^{iηA}` on □ and
`|A| < f M α₀ (ell^j η)^{-1}`, `|∇^η A| < f M α₀ (ell^j η)^{-2}`,
`|∂^{η*}∂^η A| < f M α₀ (ell^j η)^{-3}` on □.  Norm: Frobenius (the `O(1)` and the smallness
threshold absorb every norm-equivalence constant). `∇^η` = forward difference, `∂*∂` = summed
discrete Laplacian, each only where all bonds it reads lie in □. -/
def PerCubeRegular {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
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
      (∀ (ν : Fin 3) (x : PeriodicLatticeSite L),
        CubeBond sites ((x, ν) : Bond L) →
        (∀ μ : Fin 3, CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) ∧
          CubeBond sites
            ((AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack x μ, ν) :
              Bond L)) →
        frobNorm (((η⁻¹ : ℝ) ^ 2) • ∑ μ : Fin 3,
            (A (periodicLatticeShift x μ, ν)
              + A (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack x μ, ν)
              - (2 : ℝ) • A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

/-- `Λ ⊂ Λ_k = Ω_k^{(k)}`, a union of big blocks of the unit torus, with distance from `Λ_k^c`
bigger than `RM` (p.427). `Λ_k` is the set of unit sites whose fine corner `ell^k · y` lies in
`Ω_k`. -/
def LambdaOK {Lu Lf : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower Lf)
    (Lam : Set (PeriodicLatticeSite Lu)) : Prop :=
  BlockClosed M Lam ∧
  ∃ emb : PeriodicLatticeSite Lu → PeriodicLatticeSite Lf,
    (∀ y μ, (emb y μ).val = (ell ^ k) * (y μ).val) ∧
    (∀ y ∈ Lam, emb y ∈ S.Om k) ∧
    (∀ y ∈ Lam, ∀ y' : PeriodicLatticeSite Lu, emb y' ∉ S.Om k → R * M < pdist y y')

/-- `B̃ = 0` outside `Λ` (Dirichlet): bonds with an endpoint outside `Λ` carry no `B̃`. -/
def OnLambda {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu))
    (B : Bond Lu → SuTwo) : Prop :=
  ∀ b : Bond Lu, ¬ (b.1 ∈ Lam ∧ periodicLatticeShift b.1 b.2 ∈ Lam) → B b = 0

/-- `Λ'`: the coarse sites whose whole `ell`-block lies in `Λ` (CMP96/p.428: `Λ = B(Λ')`). -/
def LamPrime {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) :
    Set (PeriodicLatticeSite Lu) :=
  {y | y ∈ CoarseLattice Lu ell ∧ ∀ x ∈ blockOf y ell, x ∈ Lam}

/-- **r5 (3)**: the coarse bond `c` TOUCHES `Λ'`: at least one end-point `c₋ = c.1.1`, `c₊ = coarseShift c₋ ell μ`
lies in `Λ'`.  CMP96 p.224: "we will apply the same notations to sets of bonds ... {bonds b: at least one end-point
of b belongs to Ω}"; CMP96 p.245 L2.4: "We denote by Λ also a set of bonds b such that at least one of the end-points
b₋, b₊ belongs to Λ".  r2..r4 used `c₋ ∈ Λ'` only. -/
def CRowIn {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu))
    (c : CoarseBond Lu ell) : Prop :=
  c.1.1 ∈ LamPrime ell Lam ∨ AdalyFormal.Balaban.CoarseCurl.coarseShift c.1.1 ell c.2 ∈ LamPrime ell Lam

/-- Bonds `b₀ = B(c) ∩ c` for coarse bonds `c` TOUCHING `Λ'` (the bonds `C` solves for). -/
def IsDroppedIn {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu)) (ell : ℕ)
    (b : Bond Lu) : Prop :=
  ∃ c : CoarseBond Lu ell, CRowIn ell Lam c ∧ b = droppedBondLast ell c

/-- the dropped bond of a row that touches `Λ'` through `c₊` only is dropped (must-fire control for r5 (3):
the r2..r4 definition `c₋ ∈ Λ'` makes this false). -/
theorem droppedBond_of_cplus {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu)) (ell : ℕ)
    (c : CoarseBond Lu ell)
    (h : AdalyFormal.Balaban.CoarseCurl.coarseShift c.1.1 ell c.2 ∈ LamPrime ell Lam) :
    IsDroppedIn Lam ell (droppedBondLast ell c) := ⟨c, Or.inr h, rfl⟩

/-- `Λ̃ = Λ \ (∪_{y∈Λ'} Ax(y) ∪ ∪_{c∈Λ'} B(c)∩c)` (p.428), as the vanishing conditions on `B̃`:
the axial staircases of `y ∈ Λ'` and the dropped bonds of `c ∈ Λ'`. With `Λ` = whole torus this is
exactly `CoercUMainDesigned.OnLambdaTilde` (`onLambdaTildeIn_univ`). -/
def OnLambdaTildeIn {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu)) (ell : ℕ)
    (B : Bond Lu → SuTwo) : Prop :=
  (∀ y ∈ LamPrime ell Lam, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0) ∧
  (∀ b : Bond Lu, IsDroppedIn Lam ell b → B b = 0)

/-! ## §3 -- the ingredients of (3.156)

The print defines `Δ_k` by `(QG₁Q*)⁻¹ − a − 2⟨H₁D̃⁽²⁾(·),J⟩`, with `G₁` the covariance of
(3.138), `H₁` the variational solution operator (3.126)-(3.129), `D̃⁽²⁾` "a quadratic polynomial in
B with properties similar to C⁽²⁾(A)" (p.427), `J` the source (3.11), `Q₁`, `Ax(y)`.  Several of
these are NOT constructed in this tree (see REPORT).  They are therefore carried as DATA, with only
the laws the print itself states, in `Ingr`; the statement is a predicate OF the ingredient family,
so the prover can never choose them (S91). -/

structure Ingr (ell : ℕ) (Lu Lf : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu)) where
  /-- `Q`: fine `A`-fields → unit-lattice `B`-fields. -/
  Q : BondFnL2 Lf →L[ℝ] BondFnL2 Lu
  /-- `Q*`, carried as data with the adjoint law below (avoids the `.adjoint` instance diamond). -/
  Qs : BondFnL2 Lu →L[ℝ] BondFnL2 Lf
  G1 : BondFnL2 Lf →L[ℝ] BondFnL2 Lf
  a : ℝ
  H1 : BondFnL2 Lu →L[ℝ] BondFnL2 Lf
  /-- `D̃⁽²⁾`: quadratic in `B`. -/
  D2 : BondFnL2 Lu → BondFnL2 Lu
  J : BondFnL2 Lf
  /-- `Q₁` (printed subscript `1`; the same symbol is used in the subspace and in `δ(Q₁B)`). -/
  Q1 : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)
  /-- `C` of (3.157). -/
  C : (Bond Lu → SuTwo) →ₗ[ℝ] (Bond Lu → SuTwo)
  Qs_adj : ∀ (x : BondFnL2 Lf) (y : BondFnL2 Lu), inner ℝ (Q x) y = inner ℝ x (Qs y)
  D2_quad : ∀ (c : ℝ) (B : BondFnL2 Lu), D2 (c • B) = (c ^ 2) • D2 B
  /-- the print writes `(QG₁Q*)⁻¹`: the composite is invertible. -/
  QGQ_unit : IsUnit ((Q.comp G1).comp Qs)
  /-- p.428: "C is an identity operator on almost all bonds, except the bonds b₀". -/
  C_id : ∀ (B : Bond Lu → SuTwo) (b : Bond Lu), ¬ IsDroppedIn Lam ell b → C B b = B b
  /-- `B = C B̃` lies in `{Q₁B = 0}` (on the coarse bonds of `Λ'`). -/
  C_ker : ∀ B : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell B → OnLambda Lam B →
    ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → Q1 (C B) c = 0

/-- **(3.156)**: `⟨B,Δ_kB⟩ := ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B), J⟩`. -/
noncomputable def Ingr.form {ell : ℕ} {Lu Lf : PeriodicLatticeExtent}
    {Lam : Set (PeriodicLatticeSite Lu)} (I : Ingr ell Lu Lf Lam)
    (B : BondFnL2 Lu) : ℝ :=
  inner ℝ B (Ring.inverse ((I.Q.comp I.G1).comp I.Qs) B)
    - I.a * inner ℝ B B - 2 * inner ℝ (I.H1 (I.D2 B)) I.J

/-! ## §4 -- the statement -/

/-- Data of the dependence the print states: "the operators are defined by the sequence {Ω_j}
and a configuration U". -/
abbrev IngrFam (ell : ℕ) (Lu Lf : PeriodicLatticeExtent) : Type :=
  Tower Lf → LinkCfg Lf → (Lam : Set (PeriodicLatticeSite Lu)) → Ingr ell Lu Lf Lam

/-- Torus compatibility (owner ruling 2026-07-25 `hstrict`/`CompatibleExtent`): the blocking
operations `blockOf`/`CoarseLattice` silently truncate unless `ell ∣ N` and `ell < N`
(`torus-blockof-truncation-artifact`); big blocks of side `M` must tile too. -/
def TorusOK (ell M : ℕ) (Lu : PeriodicLatticeExtent) : Prop :=
  (∀ μ : Fin 3, ell ∣ Lu μ + 1) ∧ (∀ μ : Fin 3, ell < Lu μ + 1) ∧ (∀ μ : Fin 3, M ∣ Lu μ + 1)

/-- The claim at a FIXED `(k, Lu, Lf)`, class parameters `(f, α₀)` and constant `γ₀`:
for every admissible tower of height `k`, every `Λ`, every `U` in the per-cube class (mesh
`η = ell^{-k}`: the unit lattice has `L^k η = 1`, p.427), and every `B̃ ∈ Λ̃` supported in `Λ`:
`γ₀ ‖B̃‖² ≤ ⟨C B̃, Δ_k C B̃⟩`. -/
def CoercAt (ell M R k : ℕ) {Lu Lf : PeriodicLatticeExtent} (I : IngrFam ell Lu Lf)
    (f : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower Lf), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK ell M R k S Lam →
  ∀ (U : LinkCfg Lf), PerCubeRegular ell M f k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambda Lam Bt →
    γ₀ * bondEnergy Bt
      ≤ (I S U Lam).form (WithLp.toLp 2 ((I S U Lam).C Bt))

/-- `CoercAt` for every class parameter `f ≥ 10`, `α₀ > 0` with `f M α₀ ≤ a₀`
("`O(1) M α₀` sufficiently small", p.396/p.428), at one `γ₀`. -/
def CoercCore (ell M R k : ℕ) {Lu Lf : PeriodicLatticeExtent} (I : IngrFam ell Lu Lf)
    (a₀ γ₀ : ℝ) : Prop :=
  ∀ (f : ℕ), 10 ≤ f → ∀ (α₀ : ℝ), 0 < α₀ → (f : ℝ) * M * α₀ ≤ a₀ →
    CoercAt ell M R k I f α₀ γ₀

/-- The ingredient family for step `k` over unit torus `Lu`: its fine torus is `scaleUp ell k Lu`
by definition, so the family is never required to exist at a meaningless `(Lu, Lf)` pair. -/
abbrev IngrFamK (ell : ℕ) : Type :=
  ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), IngrFam ell Lu (scaleUp ell k Lu)

/-- **SUPERSEDED (r1 form; r5 statement `P428Genuine5` was superseded by the r6 statement `ZT5A.P428Genuine8`).** THE RESTATED CLAIM.  Fixed blocking data `(ell, M, R)` (degenerate values make it `False`);
a pinned ingredient family `I`; THERE EXIST `a₀ > 0` and `γ₀ > 0` such that for EVERY `k`, every
unit torus `Lu` (fine torus `scaleUp ell k Lu`) and everything in `CoercCore` the bound holds.
`γ₀` and `a₀` are outside every binder named in the print (`k`, `U`) and also outside the torus,
the tower, `Λ`, `f`, `α₀`. -/
def P428Faithful (ell M R : ℕ) (I : IngrFamK ell) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 0 < R) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), CoercCore ell M R k (I k Lu) a₀ γ₀

/-- The WEAKER reading in which `γ₀` may depend on the class parameters `(f, α₀)` (but is still
independent of `k`, the torus, the tower, `Λ`, `U`). -/
def P428FaithfulWeak (ell M R : ℕ) (I : IngrFamK ell) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 0 < R) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (f : ℕ), 10 ≤ f → ∀ (α₀ : ℝ), 0 < α₀ → (f : ℝ) * M * α₀ ≤ a₀ →
      ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), CoercAt ell M R k (I k Lu) f α₀ γ₀

theorem P428Faithful.weak {ell M R : ℕ} {I : IngrFamK ell} (h : P428Faithful ell M R I) :
    P428FaithfulWeak ell M R I := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, fun f hf α₀ hα hsm => ⟨γ₀, hγ, fun k Lu => h k Lu f hf α₀ hα hsm⟩⟩

/-- The same with the unit torus FIXED before `γ₀` (the weaker, volume-dependent variant). -/
def P428FaithfulFixedTorus (ell M R : ℕ) (Lu : PeriodicLatticeExtent) (I : IngrFamK ell) : Prop :=
  (2 ≤ ell ∧ 0 < M ∧ 0 < R) ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), CoercCore ell M R k (I k Lu) a₀ γ₀

theorem P428Faithful.fixedTorus {ell M R : ℕ} {I : IngrFamK ell} (h : P428Faithful ell M R I)
    (Lu : PeriodicLatticeExtent) : P428FaithfulFixedTorus ell M R Lu I := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, γ₀, hγ, fun k => h k Lu⟩

#print axioms P428Faithful.fixedTorus

#print axioms admissible_k0_om0_empty
#print axioms pdist_l1_diag
#print axioms sup_pdist_diag
#print axioms sup_le_pdist
#print axioms droppedBond_of_cplus

end AdalyFormal.StatementLane
