import R2RawX

/-!
# ZLocJet -- r8 REPAIR: the averaging jets defined PER COMPONENT (local), and the bridge to the r7 jets

**Why (statement defect 2026-10-12, `compute/u_reads_omega0_20261012`).**  r7 defined the linear part of the printed
one-step averaging as `QlinStepX s ell V0 := fderiv ℝ (qStepX s ell V0) 0`, the Frechet derivative of the map on ALL bonds of
the torus.  If ONE component `a ↦ qStepX s ell V0 a c` (any bond `c`, anywhere) is not differentiable at `0`, Mathlib's `fderiv`
of the whole map is the junk `0`, so every row vanishes, including the rows inside `Ω₀` (`UR1.QlinStepX_bad_eq_zero`).

**Repair.**  The printed linear part (CMP98 (122)/(124): `Q(V₀,A,c) = L(Q(V₀)A)_c + C(V₀,A,c)`) is a statement about EACH
component `c`.  r8 defines the jet component by component:
 * `QlinStepL s ell V0 a c := fderiv ℝ (fun a => qStepX s ell V0 a c) 0 a`  (junk at `c` only if THIS component is not differentiable);
 * the level composite by the printed chain CMP99b (3.15) "`Q_j(U) = Q(Ū^{j-1})···Q(Ū)Q(U)`":
   `QlinCompL ell bg 0 = id`, `QlinCompL ell bg (j+1) = QlinStepL (ell^j) ell (bg j) ∘ QlinCompL ell bg j`;
 * second order: `D2StepL` (per-component second derivative, bilinear), `D2CompL` by the second-order chain rule,
   `C2StepL a = ½ D2StepL a a`, `C2CompL j a = ½ D2CompL j a a`.

**Bridge** (every earlier result transfers): whenever the whole-torus map is differentiable at `0` the local jet IS the r7 jet
(`QlinStepL_eq_QlinStepX`); on a regular background tower (`RegTower`, which holds at `U = 1` and under M0's global smallness)
`QlinCompL = QlinCompX`, `C2StepL = C2StepX`, `C2CompL = C2CompX` (`QlinCompL_eq_QlinCompX`, `C2StepL_eq_C2StepX`,
`C2CompL_eq_C2CompX`).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp

variable {L : PeriodicLatticeExtent}

/-- the component of the raw one-step averaging at the bond `c`, as a function of the coordinate field. -/
noncomputable def qStepComp (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) :
    XS L → (Fin 3 → ℝ) := fun a => qStepX s ell V0 a c

/-- **r8 LOCAL first-order jet** of the one-step averaging: component `c` is the Frechet derivative of component `c`. -/
noncomputable def QlinStepL (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) : XS L →L[ℝ] XS L :=
  ContinuousLinearMap.pi (fun c => fderiv ℝ (qStepComp s ell V0 c) 0)

theorem QlinStepL_apply (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) (c : PeriodicLatticeEdge L) :
    QlinStepL s ell V0 a c = fderiv ℝ (qStepComp s ell V0 c) 0 a := rfl

/-- **BRIDGE (one step).**  If the whole-torus map is differentiable at `0`, the local jet is the r7 jet. -/
theorem QlinStepL_eq_QlinStepX (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (h : DifferentiableAt ℝ (qStepX s ell V0) 0) : QlinStepL s ell V0 = QlinStepX s ell V0 := by
  ext1 a; funext c
  rw [QlinStepL_apply, QlinStepX]
  have e : fderiv ℝ (qStepComp s ell V0 c) 0 = (ContinuousLinearMap.proj c).comp (fderiv ℝ (qStepX s ell V0) 0) :=
    fderiv_apply (Φ := qStepX s ell V0) h c
  rw [e]; rfl

/-- the bridge on a regular background (`RegBg`). -/
theorem QlinStepL_eq_of_reg (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0) :
    QlinStepL s ell V0 = QlinStepX s ell V0 :=
  QlinStepL_eq_QlinStepX s ell V0 ((qStepX_contDiffAt s ell V0 hreg).differentiableAt (by simp))

/-- **r8 LOCAL level composite** (CMP99b (3.15)): `Q_0 = id`, `Q_{j+1} = Q(Ū^j) Q_j`, each factor the local jet. -/
noncomputable def QlinCompL (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) : ℕ → (XS L →L[ℝ] XS L)
  | 0 => ContinuousLinearMap.id ℝ (XS L)
  | j + 1 => (QlinStepL (ell ^ j) ell (bg j)).comp (QlinCompL ell bg j)

theorem QlinCompL_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    QlinCompL ell bg 0 = ContinuousLinearMap.id ℝ (XS L) := rfl

theorem QlinCompL_succ (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) :
    QlinCompL ell bg (j + 1) = (QlinStepL (ell ^ j) ell (bg j)).comp (QlinCompL ell bg j) := rfl

theorem QlinCompX_zero_id (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    QlinCompX ell bg 0 = ContinuousLinearMap.id ℝ (XS L) := by
  unfold QlinCompX; exact fderiv_id

/-- **BRIDGE (composite).**  On a regular tower the local composite is the r7 composite `QlinCompX` (`fderiv` of the whole
composite map). -/
theorem QlinCompL_eq_QlinCompX (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) : ∀ j, j ≤ J → QlinCompL ell bg j = QlinCompX ell bg j := by
  intro j
  induction j with
  | zero => intro _; rw [QlinCompL_zero, QlinCompX_zero_id]
  | succ j ih =>
      intro hj
      rw [QlinCompL_succ, QlinCompX_succ ell bg J hreg j (by omega), ih (by omega),
        QlinStepL_eq_of_reg _ _ _ (hreg j (by omega))]

/-! ## second order -/

/-- per-component second derivative, as a bilinear map. -/
noncomputable def D2StepL (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) : XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L :=
  LinearMap.mk₂ ℝ (fun a b c => fderiv ℝ (fderiv ℝ (qStepComp s ell V0 c)) 0 a b)
    (fun a a' b => by funext c; simp)
    (fun r a b => by funext c; simp)
    (fun a b b' => by funext c; simp)
    (fun r a b => by funext c; simp)

theorem D2StepL_apply (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a b : XS L) (c : PeriodicLatticeEdge L) :
    D2StepL s ell V0 a b c = fderiv ℝ (fderiv ℝ (qStepComp s ell V0 c)) 0 a b := rfl

/-- **r8 LOCAL second-order term of one step**: `C(V₀,a,c) = ½ D²(component c)(0)(a,a)`. -/
noncomputable def C2StepL (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) : XS L :=
  (1 / 2 : ℝ) • D2StepL s ell V0 a a

/-- the composite bilinear second derivative by the second-order chain rule (`D2_{j+1}(a,b) = Q(Ū^j) D2_j(a,b) + D2(Ū^j)(Q_j a, Q_j b)`). -/
noncomputable def D2CompL (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)
  | 0 => 0
  | j + 1 => LinearMap.mk₂ ℝ
      (fun a b => QlinStepL (ell ^ j) ell (bg j) (D2CompL ell bg j a b)
        + D2StepL (ell ^ j) ell (bg j) (QlinCompL ell bg j a) (QlinCompL ell bg j b))
      (fun a a' b => by simp only [map_add, LinearMap.add_apply]; abel)
      (fun r a b => by simp only [map_smul, LinearMap.smul_apply, smul_add])
      (fun a b b' => by simp only [map_add, LinearMap.add_apply]; abel)
      (fun r a b => by simp only [map_smul, LinearMap.smul_apply, smul_add])

/-- **r8 LOCAL second-order term of the level composite**: `C_j(a) = ½ D2_j(a,a)`. -/
noncomputable def C2CompL (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (a : XS L) : XS L :=
  (1 / 2 : ℝ) • D2CompL ell bg j a a

theorem C2CompL_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (a : XS L) :
    C2CompL ell bg 0 a = 0 := by
  simp [C2CompL, D2CompL]

/-- the printed second-order chain rule for the local objects. -/
theorem C2CompL_succ (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (a : XS L) :
    C2CompL ell bg (j + 1) a
      = QlinStepL (ell ^ j) ell (bg j) (C2CompL ell bg j a) + C2StepL (ell ^ j) ell (bg j) (QlinCompL ell bg j a) := by
  simp only [C2CompL, C2StepL, D2CompL, LinearMap.mk₂_apply, map_smul, smul_add]

theorem C2StepL_smul (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (r : ℝ) (a : XS L) :
    C2StepL s ell V0 (r • a) = r ^ 2 • C2StepL s ell V0 a := by
  simp only [C2StepL, map_smul, LinearMap.smul_apply, smul_smul]
  congr 1; ring

/-- second-order bridge for one step: componentwise second derivative of a `C²` map. -/
theorem C2StepL_eq_C2StepX (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0) :
    C2StepL s ell V0 = C2StepX s ell V0 := by
  funext a; funext c
  have hg : ContDiffAt ℝ 2 (qStepX s ell V0) 0 := (qStepX_contDiffAt s ell V0 hreg).of_le (by simp)
  have hP : ContDiffAt ℝ 2 (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
      (qStepX s ell V0 0) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c).contDiff (n := 2)).contDiffAt
  have hc := AdalyFormal.Balaban.SmoothLog.fderiv_fderiv_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
    (qStepX s ell V0) (0 : XS L) hP hg a a
  have hcomp : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
      ∘ qStepX s ell V0) = qStepComp s ell V0 c := rfl
  rw [hcomp] at hc
  have h2 : fderiv ℝ (fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c))
      (qStepX s ell V0 0) = 0 := by
    have : fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
        = fun _ => ContinuousLinearMap.proj c := by
      funext y; exact ContinuousLinearMap.fderiv _
    rw [this]; exact fderiv_const_apply _
  rw [h2, ContinuousLinearMap.fderiv] at hc
  simp only [ContinuousLinearMap.zero_apply, zero_add, ContinuousLinearMap.proj_apply] at hc
  show (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepComp s ell V0 c)) 0 a a = ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 a a) c
  rw [hc]; rfl

theorem C2CompX_zero_eq (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (a : XS L) :
    C2CompX ell bg 0 a = 0 := by
  unfold C2CompX
  have : fderiv ℝ (qCompX ell bg 0) = fun _ => ContinuousLinearMap.id ℝ (XS L) := by
    funext y; exact fderiv_id
  rw [this, fderiv_const_apply]
  simp

/-- **BRIDGE (second order, composite).** -/
theorem C2CompL_eq_C2CompX (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) : ∀ j, j ≤ J → C2CompL ell bg j = C2CompX ell bg j := by
  intro j
  induction j with
  | zero => intro _; funext a; rw [C2CompL_zero, C2CompX_zero_eq]
  | succ j ih =>
      intro hj
      funext a
      rw [C2CompL_succ, C2CompX_succ ell bg J hreg j (by omega) a, ih (by omega),
        QlinCompL_eq_QlinCompX ell bg J hreg j (by omega),
        QlinStepL_eq_of_reg _ _ _ (hreg j (by omega)), C2StepL_eq_C2StepX _ _ _ (hreg j (by omega))]

#print axioms QlinStepL_eq_QlinStepX
#print axioms QlinStepL_eq_of_reg
#print axioms QlinCompL_eq_QlinCompX
#print axioms C2CompL_succ
#print axioms C2StepL_eq_C2StepX
#print axioms C2CompL_eq_C2CompX

end AdalyFormal.IngredientFamilyR2
