import CompactDictionary.Form

/-!
# Private dictionary for the two p.428 headlines

This module does not import RI6. The equivalence is obtained from exact form,
energy and hypothesis transport, retaining the same constants and quantifier order.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000
namespace CompactDictionary
open BalabanCompact
noncomputable section

theorem genForm_genC_eq (P : Prm) (hell : 0 < P.ell) (B : Bond P.Lu → Vec) :
    genForm P (toField (P.genC B)) =
      AdalyFormal.StatementLaneG.GenP.genForm (frozenParams P hell)
        (WithLp.toLp 2 (AdalyFormal.StatementLaneG.GenP.genC (frozenParams P hell)
          (fun b => pauli (B b)))) := by
  rw [genForm_eq P hell]
  congr 1
  apply PiLp.ext
  intro b
  exact congrFun (genC_conjugacy P hell B) b

/-- The only extra premise is torus divisibility, supplied by `TorusOK` below. -/
theorem instIneq_iff (P : Prm) (hell : 0 < P.ell) (γ : ℝ)
    (hdiv : ∀ μ, P.ell ∣ P.Lu μ + 1) :
    InstIneq P.ell P.k P.a γ P.Lu P.S P.Lam P.U ↔
      AdalyFormal.StatementLaneG.InstIneq P.ell P.k hell P.a P.Lu γ
        (towerEquiv P.S) P.Lam P.U := by
  constructor
  · intro h B htilde hsupport
    obtain ⟨B, rfl⟩ := (piPauli (Equiv.refl (Bond P.Lu))).surjective B
    have ht := (onLambdaTildeIn_iff P.ell P.Lam B hdiv).mpr htilde
    have hs := (onLambdaT_iff P.Lam B).mpr hsupport
    have hb := h B ht hs
    change γ * bondEnergy B ≤ genForm P (toField (P.genC B)) at hb
    rw [bondEnergy_eq, genForm_genC_eq P hell] at hb
    exact hb
  · intro h B htilde hsupport
    have hb := h (fun b => pauli (B b))
      ((onLambdaTildeIn_iff P.ell P.Lam B hdiv).mp htilde)
      ((onLambdaT_iff P.Lam B).mp hsupport)
    change γ * bondEnergy B ≤ genForm P (toField (P.genC B))
    rw [bondEnergy_eq, genForm_genC_eq P hell]
    exact hb

theorem coercG8At_iff (ell M R k c : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : Extent) (α γ : ℝ) :
    CoercG8At ell M R k c a Lu α γ ↔
      AdalyFormal.StatementLaneG.CoercG8At ell M R k hell a Lu c α γ := by
  constructor
  · intro h hT S
    obtain ⟨S, rfl⟩ := (towerEquiv (L := scaleUp ell k Lu)).surjective S
    intro hS Lam hL U hU
    exact (instIneq_iff ⟨ell, k, Lu, S, U, a, Lam⟩ hell γ hT.1).mp
      (h ((torusOK_iff ell M).mpr hT) S ((admissible_iff ell M R k S).mpr hS)
        Lam ((lambdaOK2_iff ell M R k S Lam).mpr hL) U
        ((classCoupled_iff ell M c k S α ((ell : ℝ) ^ k)⁻¹ U).mpr hU))
  · intro h hT S hS Lam hL U hU
    exact (instIneq_iff ⟨ell, k, Lu, S, U, a, Lam⟩ hell γ hT.1).mpr
      (h ((torusOK_iff ell M).mp hT) (towerEquiv S) ((admissible_iff ell M R k S).mp hS)
        Lam ((lambdaOK2_iff ell M R k S Lam).mp hL) U
        ((classCoupled_iff ell M c k S α ((ell : ℝ) ^ k)⁻¹ U).mp hU))

/-- Constants are transported unchanged, before k, the torus and the class data. -/
theorem core8At_iff (ell M R c : ℕ) (hell : 0 < ell) (a : ℝ) :
    P428Core8At ell M R c a ↔ AdalyFormal.StatementLaneG.P428Core8At ell M R hell a c := by
  simp only [P428Core8At, AdalyFormal.StatementLaneG.P428Core8At,
    coercG8At_iff ell M R _ c hell]

theorem core8_iff (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) :
    P428Core8 ell M R a ↔ AdalyFormal.StatementLaneG.P428Core8 ell M R hell a :=
  core8At_iff ell M R 12 hell a

theorem genuine8_iff (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) :
    P428Genuine8 ell M R a ↔ AdalyFormal.StatementLaneG.P428Genuine8 ell M R hell a :=
  and_congr (sidePow_iff ell M a) (core8_iff ell M R hell a)

/-- Exact headline dictionary, independent of either headline's proof. -/
theorem p428Target8_iff : BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8 := by
  unfold BalabanCompact.P428Target8 AdalyFormal.StatementLaneG.P428Target8
  apply forall_congr'
  intro ell
  apply forall_congr'
  intro hell
  simp only [genuine8_iff ell _ _ (by omega : 0 < ell)]

end
end CompactDictionary
