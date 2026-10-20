import ZXG3A

/-!
# ZT4A (r5) -- BASE definitions shared by the r5 statement (`ZT5A`): `GuardsUnit`, `WellDefG`, `LamBlockSum`, `LambdaOK2`.
The r4 statement defs that lived here (`InstAt`, `CoercGen2At`, `P428Genuine2*`, `P428Target*`) are REPLACED by `ZT5A` (they quantified `k = 0`, the
`ℓ^∞` distance, `c₋`-only rows and the `[10,F]` cube range).  Header below is the r4 text, kept for the quotes.
# (r4 header) `P428Genuine2`: the repaired statement (r4), on the TOUCHING-`𝔅` FORK (`fork/X*`).  NOTHING HERE PROVES THE LEMMA.

[SUPERSEDED in r5 -- r4 text retained for the quotes; the MAIN statement file is now `ZT5A.lean`.]  r4: `G4A.lean` (root) was the same statement over the OLD both-endpoint `E₀`/`𝔅` (r2/r3 modules); it is
kept as LEGACY evidence: over those modules `WellDef` is FALSE at the `k = 1` point of `K1D.PK_not_wellDef`.
[SUPERSEDED: r5 headline concludes the inequality only; see `ZT5A.InstIneq`/`InstAtWD`.]  r4 guards: `CoercGen2At` concluded `GenP.WellDefG` = r3's `WellDef` plus the three `Ring.inverse` units (`GuardsUnit`).
[Still true in r5, unchanged r4 fork definitions, `ZXR2Ops3`.]  S1 (CMP96 p.224 image): `bondsOm0` = bonds with AT LEAST ONE endpoint in `Ω₀`; `bondsLam j` = `st(Λ_j) \\ st(Ω_{j+1})`
(the literal bond-set difference of (2.3), `Ω_{j+1}` read from the geometry by `OmGe`).  Variant (i) (`st(Λ_j)` alone) makes `Q|E₀`
rank-deficient at `M=1,k=1` in the numeric toy `qrank_toy.py`.

R1.  CMP96 p.245 Lemma 2.4 (corpus/pages/CMP96_p245.md, adjudicated; image corpus/renders/CMP96_p245-23.png)
reads: "Let a set Lambda subset Z^d be a sum of blocks, Lambda = B(Lambda').  We denote by Lambda also a
set of bonds b such that at least one of the end-points b_-, b_+ belongs to Lambda."  r3 kept only the
second sentence.  Here `LamBlockSum` is the first: `Lambda = union_{y in Lambda'} B(y)`.
`M`: CMP99b p.408 (image corpus/renders/CMP99b_p408-20.png): "In [4] we have proved all theorems under
the assumption that R, M are sufficiently large.  We take these numbers as powers of L."  So the printed
relation is `M = L^m`; `ell ∣ M` is the weaker sufficient relation (both are stated).
R2.  `P428Target` / `P428TargetAll` fix the outer quantification of `(ell, M, R, F, a)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

namespace GenP

/-- the three UNITS the print takes for granted: `Δ'_a|Ω₀` on `L²(Ω₀)` (so `G'`, built with `Ring.inverse`, is a
genuine inverse), `G⁻¹` of (3.122), and `Q G Q*` (so `H` of (3.126), built with `Ring.inverse`, is a genuine
inverse product).  Without them `Ring.inverse` returns the junk value `0`. -/
def GuardsUnit (P : IngrBParams) : Prop :=
  IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)) ∧ IsUnit P.data.Ginv ∧
    IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs)

/-- feasibility: `WellDef` of r3 (hb, hG, hN) plus the three guards -/
def WellDefG (P : IngrBParams) : Prop := WellDef P ∧ GuardsUnit P

end GenP

/-- `Λ = B(Λ')` (CMP96 p.245 Lemma 2.4, first sentence): every site of `Λ` lies in the `ell`-block of a
coarse site whose whole block lies in `Λ`. -/
def LamBlockSum {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) : Prop :=
  ∀ x ∈ Lam, ∃ y ∈ LamPrime ell Lam, x ∈ blockOf y ell

theorem LamBlockSum_iff {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) :
    LamBlockSum ell Lam ↔
      Lam = ⋃ y ∈ LamPrime ell Lam, ((blockOf y ell : Finset (PeriodicLatticeSite Lu)) : Set (PeriodicLatticeSite Lu)) := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_iUnion, Finset.mem_coe]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := h x hx
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩; exact hy.2 x hxy
  · intro h x hx
    have hx' : x ∈ ⋃ y ∈ LamPrime ell Lam, ((blockOf y ell : Finset (PeriodicLatticeSite Lu)) : Set (PeriodicLatticeSite Lu)) := by
      rw [← h]; exact hx
    simp only [Set.mem_iUnion, Finset.mem_coe] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    exact ⟨y, hy, hxy⟩

/-- `Λ'` is nonempty whenever `Λ` is (so no `Λ' = ∅` instance with `Λ ≠ ∅`). -/
theorem LamBlockSum.lamPrime_nonempty {Lu : PeriodicLatticeExtent} {ell : ℕ}
    {Lam : Set (PeriodicLatticeSite Lu)} (h : LamBlockSum ell Lam) (hne : Lam.Nonempty) :
    (LamPrime ell Lam).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, _⟩ := h x hx
  exact ⟨y, hy⟩

/-- `LambdaOK` of r3 together with the printed decomposition `Λ = B(Λ')`. -/
def LambdaOK2 {Lu Lf : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower Lf)
    (Lam : Set (PeriodicLatticeSite Lu)) : Prop :=
  LambdaOK ell M R k S Lam ∧ LamBlockSum ell Lam

end AdalyFormal.StatementLaneG
