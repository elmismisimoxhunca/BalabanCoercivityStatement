import AdalyFormal.Balaban.SourceJ
import AdalyFormal.Balaban.SuTwoInner
import ZStatementP428

/-!
# IngredientJ -- the (3.11) source `J = D* η⁻² Im ∂U` as an `𝔰𝔲(2)`-valued field

Printed (image-verified in `AdalyFormal/Balaban/SourceJFaithful.lean` header against
corpus/renders/CMP99b_p392-04.png; text layer corpus/pages/CMP99b_p392.md eqs. (3.8),(3.9),(3.11)):
  `⟨A,J⟩ = Σ_{b⊂T_η} η^d tr A(b)J(b)`,  `J = D*η^{-2} Im ∂U`,  `(∂U)(p) = U(∂p)`;
  `(D*A)(x) = Σ_μ η^{-1}(R(U(x,x-ηe_μ))A(x-ηe_μ,x) - A(x,x+ηe_μ))`;  `(D*F)_μ = Σ_ν D*_ν F_{νμ}`.
The tree's `SourceJ.Jfield` is the η = 1 version with Hermitian matrix values.  Here:
  `JSU2 η U b := (-i) η^{-3} • Jfield U b`  (η^{-1} from D*, η^{-2} from the prefactor),
and we PROVE that the value lies in the anti-Hermitian presentation `suTwo` (the transport
`φ : X ↦ iX` fixed in `SuTwoInner`: `φ(ĵ) = J`, so `hsInner a ĵ = φ(a)·J = tr(A J)`).
NOT done here: the lattice weight `η^d` in the pairing (carriers are unweighted `PiLp 2`).
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamily

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SourceJ AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessY)

/-- Hermitian traceless. -/
def HTm (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Xᴴ = X ∧ Matrix.trace X = 0

theorem HTm_add {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : HTm X) (hY : HTm Y) : HTm (X + Y) :=
  ⟨by rw [conjTranspose_add, hX.1, hY.1], by rw [trace_add, hX.2, hY.2, add_zero]⟩
theorem HTm_neg {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : HTm X) : HTm (-X) :=
  ⟨by rw [conjTranspose_neg, hX.1], by rw [trace_neg, hX.2, neg_zero]⟩
theorem HTm_sub {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : HTm X) (hY : HTm Y) : HTm (X - Y) := by
  rw [sub_eq_add_neg]; exact HTm_add hX (HTm_neg hY)
theorem HTm_zero : HTm (0 : Matrix (Fin 2) (Fin 2) ℂ) := ⟨by simp, by simp⟩

theorem HTm_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ i ∈ s, HTm (f i)) : HTm (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HTm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact HTm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem trace_conj_self {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) :
    star (Matrix.trace X) = Matrix.trace X := by
  conv_lhs => rw [← hX, Matrix.trace_conjTranspose, star_star]

theorem piProj_HT {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) : HTm (piProj X) := by
  have ht := trace_conj_self hX
  refine ⟨?_, ?_⟩
  · unfold piProj
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX]
    congr 2
    rw [star_div₀, ht]; simp
  · unfold piProj
    rw [trace_sub, trace_smul, trace_one]
    simp

theorem conj_HT (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : HTm X) : HTm (conjByAmbient u X) := by
  have hUU : (u : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp u.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨?_, ?_⟩
  · rw [conjByAmbient_apply, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hX.1]
    noncomm_ring
  · rw [conjByAmbient_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, hX.2]

theorem inv_coe_eq (h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((h⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (h : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  have : h⁻¹ = star h := rfl
  rw [this]; simp [Matrix.star_eq_conjTranspose]

variable {L : PeriodicLatticeExtent}

theorem imHolonomy_herm (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (imHolonomy U p)ᴴ = imHolonomy U p := by
  unfold imHolonomy holonomyElemInv
  rw [inv_coe_eq, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp [star_div₀]
  rw [this, neg_smul, ← smul_neg, neg_sub]

theorem FnuMu_HT (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) : HTm (FnuMu U ν μ y) := by
  unfold FnuMu
  split_ifs
  · exact piProj_HT (imHolonomy_herm _ _)
  · exact HTm_neg (piProj_HT (imHolonomy_herm _ _))
  · exact HTm_zero

theorem DstarDir_HT (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν : Fin 3) (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : ∀ y, HTm (G y)) (x : PeriodicLatticeSite L) : HTm (DstarDir U ν G x) := by
  unfold DstarDir
  exact HTm_sub (conj_HT _ (hG _)) (hG _)

theorem Jfield_HT (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : HTm (Jfield U x μ) := by
  unfold Jfield
  refine HTm_sum _ _ fun ν _ => ?_
  split_ifs
  · exact HTm_zero
  · exact DstarDir_HT U ν _ (fun y => FnuMu_HT U ν μ y) x

/-- `J` of (3.11) on the anti-Hermitian `𝔰𝔲(2)` carrier, mesh `η`. -/
noncomputable def JSU2 (η : ℝ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Bond L → SuTwo := fun b =>
  ⟨((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield U b.1 b.2, by
    have h := Jfield_HT U b.1 b.2
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_smul, h.1, ← neg_smul]
      congr 1
      simp [star_mul']
    · rw [trace_smul, h.2, smul_zero]⟩

/-- Control: at the trivial background `J = 0` (tree theorem `Jsource_trivialU_eq_zero`). -/
theorem JSU2_trivial (η : ℝ) (b : Bond L) :
    JSU2 η (trivialU (L := L)) b = 0 := by
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield trivialU b.1 b.2 = 0
  have := Jsource_trivialU_eq_zero (L := L) b
  unfold Jsource at this
  rw [this, smul_zero]

/-- Control (non-degeneracy): at the tree's non-flat `witnessU`, `J ≠ 0` for every `η ≠ 0`. -/
theorem JSU2_witness_ne_zero (η : ℝ) (hη : η ≠ 0) :
    ∃ b, JSU2 η witnessU b ≠ 0 := by
  have hb : Jsource witnessU (witnessY, (0 : Fin 3)) ≠ 0 := Jsource_witnessU_ne_zero
  refine ⟨(witnessY, (0 : Fin 3)), fun h0 => hb ?_⟩
  have h1 : ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield witnessU witnessY 0 = 0 :=
    congrArg Subtype.val h0
  have hc : ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) ≠ 0 := by
    simp [hη]
  exact (smul_eq_zero.mp h1).resolve_left hc

#print axioms JSU2
#print axioms Jfield_HT
#print axioms JSU2_trivial
#print axioms JSU2_witness_ne_zero

end AdalyFormal.IngredientFamily
