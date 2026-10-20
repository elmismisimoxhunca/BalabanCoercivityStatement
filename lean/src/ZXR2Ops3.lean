import ZR2Ops2

/-!
# R2Ops3 -- the Dirichlet bond space `E₀`, the constraint space `𝔅`, and the assembled `BaseDataS`

`E₀ = L²(Ω₀ bonds)`: bond fields supported on bonds with both endpoints in `Ω₀` ("configurations
defined on `Ω₀`", p.393-394, p.417).  `F = L²(𝔅)`, `𝔅 = ∪_j Λ_j` realised as the Σ-type of level-`j`
bonds `b` with both endpoints in `Λ_j` (bond `(y,μ)` at level `j` is `[y, y + ell^j e_μ]`).
The bond-sector inputs (`Qfull`, `C2full`) are produced from the printed raw map in `R2Raw.lean`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-- Bonds with AT LEAST ONE endpoint in `Ω₀` (CMP96 p.224, sentence before (2.3): "If Ω ⊂ T_η, then we denote by
Ω also the set of bonds ∪_{x∈Ω} st(x) = {bonds b ⊂ T_η: at least one end-point of b belongs to Ω}").
r4 FORK: r2/r3 had BOTH endpoints. -/
def bondsOm0 (G : TowerGeom L) : Set (Bond L) :=
  {b | b.1 ∈ G.Om0 ∨ periodicLatticeShift b.1 b.2 ∈ G.Om0}

/-- `E₀ ⊂ BondFnL2 L`: bond fields supported in `Ω₀`. -/
def bondSupp (G : TowerGeom L) : Submodule ℝ (BondFnL2 L) where
  carrier := {A | ∀ b : Bond L, b ∉ bondsOm0 G → A b = 0}
  zero_mem' := fun b _ => by simp
  add_mem' := fun {A B} hA hB b hb => by simp [hA b hb, hB b hb]
  smul_mem' := fun c A hA b hb => by simp [hA b hb]

/-- `x ∈ Ω_j`, read off the tower geometry: some `ell^i`-block (`j ≤ i ≤ k`) based at a point of `Λ_i` contains `x`
(`Ω_i \ Ω_{i+1} = B^i(Λ_i)`, CMP99b p.393).  For `j > k` this is empty (`Ω_{k+1} = ∅`). -/
def OmGe (G : TowerGeom L) (j : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  ∃ i : ℕ, j ≤ i ∧ i ≤ G.k ∧ ∃ y ∈ G.Lam i, ∀ μ : Fin 3,
    (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + G.ell ^ i

theorem not_OmGe_of_lt {G : TowerGeom L} {j : ℕ} (hj : G.k < j) (x : PeriodicLatticeSite L) : ¬ OmGe G j x := by
  rintro ⟨i, h1, h2, -⟩
  omega

/-- Level-`j` bonds of `𝔅` = the literal bond-set difference of CMP96 (2.3) read with the p.224 convention:
`st(Λ_j) \ st(Ω_{j+1})` -- bonds (at stride `ell^j`) with AT LEAST ONE endpoint in `Λ_j` and NO endpoint in `Ω_{j+1}`.
r4 FORK (variant (ii)); r2/r3 had BOTH endpoints in `Λ_j`.  [Variant (i), `st(Λ_j)` alone, makes `Q|E₀` rank-deficient at
`M=1, k=1` in the numeric toy `qrank_toy.py`.] -/
def bondsLam (G : TowerGeom L) (j : ℕ) : Set (Bond L) :=
  {b | (b.1 ∈ G.Lam j ∨ coarseShift b.1 (G.ell ^ j) b.2 ∈ G.Lam j) ∧
    ¬ (OmGe G (j + 1) b.1 ∨ OmGe G (j + 1) (coarseShift b.1 (G.ell ^ j) b.2))}

/-- Index set of `𝔅`: pairs (level `j ≤ k`, level-`j` bond). -/
abbrev BIdx (G : TowerGeom L) : Type := Σ j : Fin (G.k + 1), {b : Bond L // b ∈ bondsLam G j}

noncomputable instance (G : TowerGeom L) : Fintype (BIdx G) := by
  classical
  exact inferInstance

/-- `L²(𝔅, 𝔰𝔲(2))`. -/
abbrev FSp (G : TowerGeom L) : Type := PiLp 2 (fun _ : BIdx G => SuTwo)

/-- Diagonal scaling of `𝔅`-configurations by a weight function. -/
noncomputable def diagW (G : TowerGeom L) (w : BIdx G → ℝ) : FSp G →L[ℝ] FSp G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun p => w p • (WithLp.ofLp f) p)
      map_add' := fun f g => by
        refine PiLp.ext (fun p => ?_)
        simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun p => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, WithLp.ofLp_toLp]
        exact smul_comm (w p) c ((WithLp.ofLp f) p) }

theorem diagW_symm (G : TowerGeom L) (w : BIdx G → ℝ) (f g : FSp G) :
    ⟪diagW G w f, g⟫ = ⟪f, diagW G w g⟫ := by
  simp only [PiLp.inner_apply, diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [real_inner_smul_left, real_inner_smul_right]

theorem inner_diagW (G : TowerGeom L) (w : BIdx G → ℝ) (f : FSp G) :
    ⟪f, diagW G w f⟫ = ∑ p, w p * ‖f p‖ ^ 2 := by
  simp only [PiLp.inner_apply, diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [real_inner_smul_right, real_inner_self_eq_norm_sq, mul_comm]

/-- Bond-sector inputs of the print: the constraint operator `Q = (Q_j(U))_j` on `𝔅` (3.15)/(3.110)
and the quadratic function `C^{(2)}` at bonds of `𝔅` (3.127). Produced from jets in `R2Raw`. -/
structure BondSector (G : TowerGeom L) where
  Qfull : BondFnL2 L →L[ℝ] FSp G
  C2full : BondFnL2 L → FSp G
  C2_quad : IsQuadMap C2full

/-- Weights of (3.16): `a · L^{j(d−2)}` at level `j` (`d = 3`, η-free body). -/
noncomputable def massW (G : TowerGeom L) (a : ℝ) : BIdx G → ℝ :=
  fun p => a * (G.ell : ℝ) ^ (p.1 : ℕ)

/-- `Q* a Q` (3.16) on all fine bonds. -/
noncomputable def MassFull (G : TowerGeom L) (a : ℝ) (S : BondSector G) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint S.Qfull).comp ((diagW G (massW G a)).comp S.Qfull)

theorem MassFull_symm (G : TowerGeom L) (a : ℝ) (S : BondSector G) (x y : BondFnL2 L) :
    ⟪MassFull G a S x, y⟫ = ⟪x, MassFull G a S y⟫ := by
  simp only [MassFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact diagW_symm G _ _ _

/-- The printed form (3.16): `⟨A,Q*aQA⟩ = Σ_j a Σ_{b∈Λ_j} L^{j(d-2)} |(Q_jA)(b)|²`. -/
theorem inner_MassFull (G : TowerGeom L) (a : ℝ) (S : BondSector G) (A : BondFnL2 L) :
    ⟪A, MassFull G a S A⟫ = ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖S.Qfull A p‖ ^ 2 := by
  simp only [MassFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [inner_diagW]
  rfl

/-- `E₀` carriers. -/
noncomputable def iE (G : TowerGeom L) : ↥(bondSupp G) →L[ℝ] BondFnL2 L := (bondSupp G).subtypeL
/-- `P_{E₀} = ι*` (the orthogonal projection onto `E₀`, as the adjoint of the inclusion). -/
noncomputable def pE (G : TowerGeom L) : BondFnL2 L →L[ℝ] ↥(bondSupp G) :=
  ContinuousLinearMap.adjoint (iE G)

theorem pE_inner_left (G : TowerGeom L) (x : ↥(bondSupp G)) (y : BondFnL2 L) :
    ⟪pE G y, x⟫ = ⟪y, iE G x⟫ := by
  rw [pE, ContinuousLinearMap.adjoint_inner_left]

theorem pE_inner_right (G : TowerGeom L) (x : ↥(bondSupp G)) (y : BondFnL2 L) :
    ⟪x, pE G y⟫ = ⟪iE G x, y⟫ := by
  rw [pE, ContinuousLinearMap.adjoint_inner_right]

/-- THE BASE DATA of (3.122)-(3.128), assembled from the printed operators, on `E₀`.
`C2 = C^{(2)}_π`: `C^{(2)}(A − D G' R D* A) = C2full (W A)` (3.128, second line). -/
noncomputable def baseData (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G)
    (Jf : BondFnL2 L) : BaseDataS ↥(bondSupp G) (SiteL2 L) (FSp G) where
  Dpi := (pE G).comp ((DpiFull G U a).comp (iE G))
  T := (Tfull G U).comp (iE G)
  Ts := ContinuousLinearMap.adjoint ((Tfull G U).comp (iE G))
  Q := S.Qfull.comp (iE G)
  Qs := ContinuousLinearMap.adjoint (S.Qfull.comp (iE G))
  Mass := (pE G).comp ((MassFull G a S).comp (iE G))
  C2 := fun A => S.C2full (Wop G U a (iE G A))
  J := pE G Jf
  T_adj := fun x s => by rw [ContinuousLinearMap.adjoint_inner_right]
  Q_adj := fun x y => by rw [ContinuousLinearMap.adjoint_inner_right]
  Mass_symm := fun x y => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_left, pE_inner_right]
    exact MassFull_symm G a S _ _

end AdalyFormal.IngredientFamilyR2
