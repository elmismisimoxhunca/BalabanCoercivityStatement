import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.CovariantOperators

/-!
# R2Raw1 -- the printed one-step raw averaging `V̿₁` of CMP98 (63)/(89), at SU(2), with background

Sources (page images/text read this session): CMP98 (58) [axial gauge condition and the product
`(R_{0,y}V')(Γ_{y,x}) = ∏_{b⊂Γ_{y,x}} R(V₀(Γ_{y,b₋}))V'_b`] printed p.27; (59),(61),(62) p.27-28;
(63) p.28; (82)-(83), (89)-(92) p.30-32 (corpus/mathpix normalized p27,p28,p32; adjudicated
corpus/pages CMP98_p29,p30,p31); (121)-(126) p.36 (corpus/pages/CMP98_p36.md).

(63), verbatim from corpus/mathpix/…CMP98…/normalized/p28.md (machine draft; image of p.28 read in
`compute/sol_q1_gate/renders/CMP98_p27_p28-12.png` by earlier lanes):
  `V̄_c (V̄₀)_c⁻¹ = exp[−i Σ_{x∈B(c₋)} L^{-d} (1/i) log (R_{0,c₋}V₁)(Γ_{c₋,x})] (V̄₁V₀)_c (V̄₀)_c⁻¹
                   · R̄_{0,c} exp[ i Σ_{x'∈B(c₊)} L^{-d} (1/i) log (R_{0,c₊}V₁)(Γ_{c₊,x'}) ]`,
`R̄_{0,c} = R((V̄₀)_c)`; (89): `V̿_c = (R̄_{0,c₋}V₁)⁻¹(V̄₁V₀)_c(V̄₀)_c⁻¹ R̄_{0,c} R̄_{0,c₊}V₁`.
The `i`/`(1/i)` cancel (`SuTwoLogExpCore`, `BlockingLinkEstimate` header): the SU(2) chart here is the
ordinary anti-Hermitian `su2Log`/`su2Exp`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Exp_zero)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS)

variable {L : PeriodicLatticeExtent}

/-- `∏_{b⊂Γ} R(V₀(Γ_{y,b₋})) V₁_b` (58), path-ordered, with the prefix holonomy `h = V₀(Γ_{y,b₋})`
accumulated: each factor is `h V₁_b h⁻¹ = R(h)V₁_b`. -/
def rProdAux (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) :
    SU2 → PeriodicLatticeSite L → List (Fin 3) → SU2
  | _, _, [] => 1
  | h, y, μ :: rest =>
      (h * V1 (y, μ) * h⁻¹) * rProdAux s V0 V1 (h * V0 (y, μ)) (coarseShift y s μ) rest

/-- `(R_{0,y}V₁)(Γ_{y,x})` for a path `p` from `y`. -/
def rProd (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) : SU2 :=
  rProdAux s V0 V1 1 y p

/-- THE TELESCOPING IDENTITY: `∏ R(V₀(Γ_{y,b₋}))V₁_b = (V₁V₀)(Γ) · V₀(Γ)⁻¹`. -/
theorem rProdAux_eq (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (p : List (Fin 3)) :
    ∀ (h : SU2) (y : PeriodicLatticeSite L),
      rProdAux s V0 V1 h y p
        = h * coarsePathHolonomy s (fun b => V1 b * V0 b) y p * (coarsePathHolonomy s V0 y p)⁻¹
          * h⁻¹ := by
  induction p with
  | nil => intro h y; simp [rProdAux, coarsePathHolonomy]
  | cons μ rest ih =>
      intro h y
      rw [rProdAux, ih]
      simp only [coarsePathHolonomy, mul_inv_rev]
      group

theorem rProd_eq (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    rProd s V0 V1 y p
      = coarsePathHolonomy s (fun b => V1 b * V0 b) y p * (coarsePathHolonomy s V0 y p)⁻¹ := by
  rw [rProd, rProdAux_eq]; simp

/-- `Σ_{x∈B(y)} L^{-d} log (R_{0,y}V₁)(Γ_{y,x})`  (`d = 3`; ℚ-scaling as in `stridedBlockedGauge`). -/
noncomputable def sBlock (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) : M2 :=
  ∑ x ∈ stepBlockOf y s ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (rProd s V0 V1 y (coarseGammaPath s y x))

/-- **The raw one-step averaging `V̿₁ = \\overline{\\overline{R(V₀)V₁}}`, (63)/(89)**, at SU(2):
`V̿_c = exp[−S₋] (V̄₁V₀)_c (V̄₀)_c⁻¹ · R̄_{0,c}(exp S₊)`, `R̄_{0,c} g = (V̄₀)_c g (V̄₀)_c⁻¹`. -/
noncomputable def rawStep (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) :
    PeriodicLinkConfiguration SU2 L := fun c =>
  su2Exp (-(sBlock s ell V0 V1 c.1))
    * (stridedBlockedGauge su2LogExp s ell (fun b => V1 b * V0 b) c
        * (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹)
    * (stridedBlockedGauge su2LogExp s ell V0 c * su2Exp (sBlock s ell V0 V1 (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹)

/-- The simplification `V̿_c = exp[−S₋](V̄₁V₀)_c exp[S₊](V̄₀)_c⁻¹`. -/
theorem rawStep_simp (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) :
    rawStep s ell V0 V1 c
      = su2Exp (-(sBlock s ell V0 V1 c.1))
        * stridedBlockedGauge su2LogExp s ell (fun b => V1 b * V0 b) c
        * su2Exp (sBlock s ell V0 V1 (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹ := by
  unfold rawStep
  group

/-- `V₁ = 1` ⇒ `rProd = 1`. -/
theorem rProd_one_right (s : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) : rProd s V0 (fun _ => 1) y p = 1 := by
  rw [rProd_eq]
  simp

/-- The raw averaging fixes the identity configuration: `V̿(V₁ = 1) = 1` (every `V₀`). -/
theorem rawStep_one_right (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) : rawStep s ell V0 (fun _ => 1) c = 1 := by
  rw [rawStep_simp]
  have hs : ∀ y, sBlock s ell V0 (fun _ => 1) y = 0 := by
    intro y
    unfold sBlock
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [rProd_one_right]; simp
  rw [hs, hs, neg_zero, su2Exp_zero]
  have : (fun b => (1 : SU2) * V0 b) = V0 := by funext b; simp
  rw [this]
  simp

#print axioms rProdAux_eq
#print axioms rProd_eq
#print axioms rawStep_simp
#print axioms rawStep_one_right

end AdalyFormal.IngredientFamilyR2
