import R2Raw3
import R2Coord
import SmoothLogJet2

/-!
# R2RawX -- analysis of the raw one-step averaging in real coordinates `X = Edge → ℝ³`

All smoothness / jet statements live on `XS L = Edge → (Fin 3 → ℝ)` (ordinary normed space, no
subtype, no guard): `toM2 : ℝ³ → 𝔰𝔲(2) ⊂ M₂(ℂ)` (R2Coord) turns a coordinate field into an
su(2)-valued field, `su2Exp (toM2 a)` is then genuinely `exp (toM2 a)` (guard transparent).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.SmoothLog (su2Log_comp_contDiffAt fderiv_fderiv_comp)

variable {L : PeriodicLatticeExtent}

/-- coordinate fields `Edge → ℝ³` -/
abbrev XS (L : PeriodicLatticeExtent) : Type := PeriodicLatticeEdge L → (Fin 3 → ℝ)

noncomputable def toM2L : (Fin 3 → ℝ) →L[ℝ] M2 := LinearMap.toContinuousLinearMap toM2
noncomputable def fromM2L : M2 →L[ℝ] (Fin 3 → ℝ) := LinearMap.toContinuousLinearMap fromM2

theorem toM2L_apply (v : Fin 3 → ℝ) : toM2L v = toM2 v := rfl
theorem fromM2L_apply (X : M2) : fromM2L X = fromM2 X := rfl

/-- the group configuration `exp (toM2 a)`. -/
noncomputable def expCfgX (a : XS L) : PeriodicLinkConfiguration SU2 L :=
  fun b => su2Exp (toM2 (a b))

theorem expCfgX_zero : (expCfgX (0 : XS L)) = fun _ => 1 := by
  funext b; simp [expCfgX]

theorem SG_expCfgX (b : PeriodicLatticeEdge L) : SG (fun a : XS L => expCfgX a b) := by
  have hS : ContDiffAt ℝ ⊤ (fun a : XS L => toM2L (a b)) 0 :=
    toM2L.contDiff.contDiffAt.comp (0 : XS L) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b).contDiff.contDiffAt
  exact SG_su2Exp (S := fun a : XS L => toM2L (a b)) hS
    (fun a => (toM2_mem (a b)).1) (fun a => (toM2_mem (a b)).2)

noncomputable def prodCfgX (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) :
    PeriodicLinkConfiguration SU2 L := fun b => expCfgX a b * V0 b

theorem SG_prodCfgX (V0 : PeriodicLinkConfiguration SU2 L) (b : PeriodicLatticeEdge L) :
    SG (fun a : XS L => prodCfgX V0 a b) :=
  (SG_expCfgX b).mul (SG.const (V0 b))

/-- A background is REGULAR (at stride `s`, blocking `ell`) when all loops of the (43)-average lie
in `LogReg`: this is where "`Mα₀` sufficiently small" enters. -/
def RegBg (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L), x ∈ stepBlockOf c.1 s ell →
    ((loopVar s ell V0 c x : SU2) : M2) ∈ LogReg

/-- `su2Log` values lie in `𝔰𝔲(2)`. -/
theorem su2Log_mem_suTwo (g : SU2) : su2Log g ∈ suTwo :=
  ⟨su2Log_antiHermitian g, su2Log_traceless g⟩

theorem sum_qsmul_su2Log_mem {ι : Type*} (s : Finset ι) (q : ℚ) (g : ι → SU2) :
    (∑ i ∈ s, q • su2Log (g i)) ∈ suTwo := by
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [qsmul_real]
  exact Submodule.smul_mem _ _ (su2Log_mem_suTwo _)

/-- `A ↦ su2Exp (Σ_x q • su2Log (G_x A))` is analytic at `0` when each `G_x` is analytic at `0`
with `G_x 0` in `LogReg`. -/
theorem SG_su2Exp_sum_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (q : ℚ) (G : ι → E → SU2) (hG : ∀ i ∈ s, SG (G i))
    (hreg : ∀ i ∈ s, (((G i 0 : SU2)) : M2) ∈ LogReg) :
    SG (fun A => su2Exp (∑ i ∈ s, q • su2Log (G i A))) := by
  refine SG_su2Exp ?_ (fun A => (sum_qsmul_su2Log_mem s q (fun i => G i A)).1)
    (fun A => (sum_qsmul_su2Log_mem s q (fun i => G i A)).2)
  refine ContDiffAt.sum (fun i hi => ?_)
  simp only [qsmul_real]
  exact (su2Log_comp_contDiffAt_reg (G i) le_rfl (hG i hi) (hreg i hi)).const_smul _


theorem prodCfgX_zero (V0 : PeriodicLinkConfiguration SU2 L) : prodCfgX V0 (0 : XS L) = V0 := by
  funext b; simp [prodCfgX, expCfgX_zero]

theorem SG_loopVar (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    SG (fun A : XS L => loopVar s ell (prodCfgX V0 A) c x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SG.hol (E := XS L) s (fun A => prodCfgX V0 A) (fun b => SG_prodCfgX V0 b) p y
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv

/-- the (43)-average of `V₁V₀` is analytic at `A = 0` on a regular background. -/
theorem SG_avg_prod (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0)
    (c : PeriodicLatticeEdge L) :
    SG (fun A : XS L => stridedBlockedGauge su2LogExp s ell (prodCfgX V0 A) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SG.hol (E := XS L) s (fun A => prodCfgX V0 A) (fun b => SG_prodCfgX V0 b) p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log (E := XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x A => loopVar s ell (prodCfgX V0 A) c x) (fun x _ => SG_loopVar s ell V0 c x)
    (fun x hx => by rw [prodCfgX_zero]; exact hreg c x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this

/-- the constant factor `(V̄₀)_c⁻¹`. -/
theorem SG_avg_const_inv (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) :
    SG (fun _ : XS L => (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹) := SG.const _

theorem SG_rProd (s : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    SG (fun A : XS L => rProd s V0 (expCfgX A) y p) := by
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SG.hol (E := XS L) s (fun A => prodCfgX V0 A) (fun b => SG_prodCfgX V0 b) p y
  have h0 := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SG.hol (E := XS L) s (fun _ => V0) (fun b => SG.const (V0 b)) p y
  have : (fun A : XS L => rProd s V0 (expCfgX A) y p)
      = fun A => coarsePathHolonomy s (prodCfgX V0 A) y p * (coarsePathHolonomy s V0 y p)⁻¹ := by
    funext A; exact rProd_eq s V0 (expCfgX A) y p
  rw [this]
  exact SG.mul_inv (h p y) (SG.const _)

open AdalyFormal.IngredientFamilyR2 in
theorem rProd_expCfgX_zero (s : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) : rProd s V0 (expCfgX (0 : XS L)) y p = 1 := by
  rw [expCfgX_zero]; exact rProd_one_right s V0 y p

/-- `A ↦ su2Exp (± Σ_x q • su2Log (R_{0,y}V₁)(Γ_{y,x}))` is analytic (all logs are based at `1`). -/
theorem SG_su2Exp_sBlock (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) :
    SG (fun A : XS L => su2Exp (sBlock s ell V0 (expCfgX A) y)) := by
  unfold sBlock
  have := SG_su2Exp_sum_log (E := XS L) (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x A => rProd s V0 (expCfgX A) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd s V0 y _)
    (fun x _ => by
      show ((rProd s V0 (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
  exact this

theorem SG_su2Exp_neg_sBlock (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) :
    SG (fun A : XS L => su2Exp (-(sBlock s ell V0 (expCfgX A) y))) := by
  have := SG_su2Exp_sum_log (E := XS L) (stepBlockOf y s ell) (-((ell : ℚ) ^ 3)⁻¹)
    (fun x A => rProd s V0 (expCfgX A) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd s V0 y _)
    (fun x _ => by
      show ((rProd s V0 (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
  unfold sBlock
  simpa [neg_smul, Finset.sum_neg_distrib] using this

/-- THE RAW ONE-STEP AVERAGING IS ANALYTIC AT `A = 0` ON A REGULAR BACKGROUND. -/
theorem SG_rawStep (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0)
    (c : PeriodicLatticeEdge L) :
    SG (fun A : XS L => rawStep s ell V0 (expCfgX A) c) := by
  have e : (fun A : XS L => rawStep s ell V0 (expCfgX A) c)
      = fun A => su2Exp (-(sBlock s ell V0 (expCfgX A) c.1))
        * stridedBlockedGauge su2LogExp s ell (prodCfgX V0 A) c
        * su2Exp (sBlock s ell V0 (expCfgX A) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹ := by
    funext A; exact rawStep_simp s ell V0 (expCfgX A) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock s ell V0 c.1
  have h2 := SG_avg_prod s ell V0 hreg c
  have h3 := SG_su2Exp_sBlock s ell V0 (cPlusS s ell c)
  have h4 := SG_avg_const_inv s ell V0 c
  exact (((h1.mul h2).mul h3).mul h4)

theorem rawStep_expCfgX_zero (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) : rawStep s ell V0 (expCfgX (0 : XS L)) c = 1 := by
  rw [expCfgX_zero]; exact rawStep_one_right s ell V0 c

#print axioms SG_rawStep
#print axioms SG_avg_prod
#print axioms SG_su2Exp_sBlock


/-- `Q_step(V₀,a)_c = fromM2 (su2Log (V̿₁(exp a))_c)` — the Lie-algebra chart of CMP98 (121), in
coordinates. -/
noncomputable def qStepX (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) : XS L :=
  fun c => fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c))

theorem qStepX_zero (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) :
    qStepX s ell V0 (0 : XS L) = 0 := by
  funext c
  simp only [qStepX, rawStep_expCfgX_zero, su2Log_one, map_zero]
  rfl

theorem qStepX_contDiffAt (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (hreg : RegBg s ell V0) : ContDiffAt ℝ ⊤ (qStepX s ell V0) 0 := by
  refine contDiffAt_pi.mpr (fun c => ?_)
  have h1 : ContDiffAt ℝ ⊤ (fun a : XS L => su2Log (rawStep s ell V0 (expCfgX a) c)) 0 :=
    su2Log_comp_contDiffAt (G := fun a : XS L => rawStep s ell V0 (expCfgX a) c)
      (SG_rawStep s ell V0 hreg c) (rawStep_expCfgX_zero s ell V0 c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : XS L) h1

/-- the linear part `L Q(V₀)` of (122), `D qStepX(0)`. -/
noncomputable def QlinStepX (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) : XS L →L[ℝ] XS L :=
  fderiv ℝ (qStepX s ell V0) 0

/-- the second-order term `C(V₀,a,c)` of (122), `½ D² qStepX(0)(a,a)`. -/
noncomputable def C2StepX (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) : XS L :=
  (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 a a

/-- level composites of (91)/(3.13): `Q_{j+1,raw} = Q_step(Ū^j) ∘ Q_{j,raw}`, `Q_{0,raw} = id`. -/
noncomputable def qCompX (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ℕ → XS L → XS L
  | 0 => id
  | j + 1 => qStepX (ell ^ j) ell (bg j) ∘ qCompX ell bg j

theorem qCompX_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) :
    qCompX ell bg j (0 : XS L) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [qCompX, Function.comp_apply, ih, qStepX_zero]

/-- regularity of the background tower up to level `J` (the smallness hypothesis of p.428). -/
def RegTower (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ) : Prop :=
  ∀ j, j < J → RegBg (ell ^ j) ell (bg j)

theorem qCompX_contDiffAt (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) : ∀ j, j ≤ J → ContDiffAt ℝ ⊤ (qCompX ell bg j) 0 := by
  intro j
  induction j with
  | zero => intro _; exact contDiffAt_id
  | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := qStepX_contDiffAt (ell ^ j) ell (bg j) (hreg j (by omega))
      have h2' : ContDiffAt ℝ ⊤ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) := by
        rw [qCompX_zero]; exact h2
      exact h2'.comp (0 : XS L) h1

/-- first-order jet of the level-`j` composite (3.13): `L^j Q_j(U)` (CMP99b (3.14)). -/
noncomputable def QlinCompX (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) :
    XS L →L[ℝ] XS L := fderiv ℝ (qCompX ell bg j) 0

/-- second-order jet of the level-`j` composite (3.13): `C_j^{raw}`. -/
noncomputable def C2CompX (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (a : XS L) :
    XS L := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qCompX ell bg j)) 0 a a

/-- CHAIN RULE: `Q_{j+1} = Q(Ū^j) Q_j`, i.e. the printed composite (3.15). -/
theorem QlinCompX_succ (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) (j : ℕ) (hj : j < J) :
    QlinCompX ell bg (j + 1) = (QlinStepX (ell ^ j) ell (bg j)).comp (QlinCompX ell bg j) := by
  have h1 := qCompX_contDiffAt ell bg J hreg j hj.le
  have h2 := qStepX_contDiffAt (ell ^ j) ell (bg j) (hreg j hj)
  have h2' : ContDiffAt ℝ ⊤ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) := by
    rw [qCompX_zero]; exact h2
  have hd1 : DifferentiableAt ℝ (qCompX ell bg j) 0 := h1.differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) :=
    h2'.differentiableAt (by simp)
  unfold QlinCompX QlinStepX
  show fderiv ℝ (qStepX (ell ^ j) ell (bg j) ∘ qCompX ell bg j) 0 = _
  rw [fderiv_comp (0 : XS L) hd2 hd1, qCompX_zero]

/-- SECOND-ORDER CHAIN RULE: `C_{j+1}(a) = Q(Ū^j) C_j(a) + C(Ū^j, Q_j a)`. -/
theorem C2CompX_succ (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) (j : ℕ) (hj : j < J) (a : XS L) :
    C2CompX ell bg (j + 1) a
      = QlinStepX (ell ^ j) ell (bg j) (C2CompX ell bg j a)
        + C2StepX (ell ^ j) ell (bg j) (QlinCompX ell bg j a) := by
  have h1 := qCompX_contDiffAt ell bg J hreg j hj.le
  have h2 := qStepX_contDiffAt (ell ^ j) ell (bg j) (hreg j hj)
  have h2' : ContDiffAt ℝ ⊤ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) := by
    rw [qCompX_zero]; exact h2
  have hc := fderiv_fderiv_comp (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j) (0 : XS L)
    (h2'.of_le (by simp)) (h1.of_le (by simp)) a a
  unfold C2CompX C2StepX QlinCompX QlinStepX
  show (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX (ell ^ j) ell (bg j) ∘ qCompX ell bg j)) 0 a a = _
  rw [hc, qCompX_zero]
  simp only [map_smul, smul_add]
  abel

#print axioms qStepX_contDiffAt
#print axioms qCompX_contDiffAt
#print axioms QlinCompX_succ

end AdalyFormal.IngredientFamilyR2
