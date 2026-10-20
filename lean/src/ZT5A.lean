import ZT4F
import ZOmGe
import ZR6A

/-!
# ZT5A -- THE r6 STATEMENT: `P428Genuine8` (CMP99b p.428 `C*Δ_kC ≥ γ₀`), with named variants and the implications between them.
NOTHING HERE PROVES THE LEMMA.  (Module name kept from r5; declarations renamed `…5 → …6`.)  Base: the r5 statement (`P428Genuine5`, commit 51402f4f57),
whose four print-supported changes over r4 are KEPT:

 (1) `pdist` = periodic `ℓ¹` distance (`ZStatementP428.pdist`; CMP96 p.223);
 (2) depth `k ≥ 1` and `Ω₀` = the p.396 collar for EVERY `k` (`Admissible`'s last conjunct is unguarded; `admissible_k0_om0_empty`);
     the headline quantifies `∀ k, 1 ≤ k → ...`;
 (3) rows `c` use the TOUCHING convention: `CRowIn` (`c₋ ∈ Λ'` or `c₊ ∈ Λ'`) in `IsDroppedIn`, `Ingr.C_ker`, `Dset`;
 (4) ONE fixed cube factor `c = 12` (`PerCubeRegular2 .. 12 ..`; CMP99b p.409);

and (6) the conclusion of the HEADLINE is the printed claim only (the lower bound `γ₀ ‖B̃‖² ≤ ⟨C B̃, Δ_k C B̃⟩`); the r4 form with the invertibility
conjunct `WellDefG` in the conclusion is the NAMED variant `…WD`, with `…WD.toHead` proved.
Kept from r4: `LamBlockSum` (Λ = B(Λ')), quantifier order `(ell, a)` first, then `m₀`, `R₀`; `a₀` and `γ₀` independent of `k, Lu, α₀, S, Λ, U, B̃`.

**r6 CHANGES (statement-audit r5, Opus: `P428Genuine5` was BROKEN, see `compute/statement_audit_r5_opus/VERDICT.md`):**
 (R1) the operators `Δ` (3.10) and `J` (3.11), and everything built on them (`Δ_π`, `DpiFull`, the `H₀`/`Nmat` chain, `genForm`, `Cop`), are
      PLAQUETTE-LOCALISED to `plaqIn Ω₀` (all four boundary bonds with BOTH endpoints in `Ω₀`) (`ZLocOps`, `ZLocJ`, `ZR2Ops2.Delta`, `ZXR2Wire2.Jf`).
      **`plaqIn` is the lane's READING of CMP99b p.394 ("They depend on the configuration U restricted to Ω₀ ... All operators we will consider will be defined by using
      Dirichlet boundary conditions on Ω₀"), NOT the printed wording.**  The print writes the Dirichlet sandwich `Ω₀Δ'_aΩ₀` for the SITE operator only and prints
      (3.10),(3.11) as sums over all `p ⊂ T_η`.  The literal sandwich on the touching bond set is the r5 operator (false: r5 collapse), and the "all four bonds touch
      Ω₀" reading is false too (concave corner of a staircase `Ω₀`: `(a + cos θ)‖X‖²`, statement_audit_r6_opus attack 2(b)); so `plaqIn` is the only surviving one of
      the readings examined.  That is a PAPER argument, not a Lean theorem; the owner-facing note is `compute/statement_lane_20261009_r7/REPORT.md` §F1;
 (R2) the coverage hypothesis is `CoversOm0p` = sites AND plaquettes (`ZR6A`): every plaquette of `Ω₀` has its four boundary bonds in ONE class cube.
 **r8 (statement defect 2026-10-12)**: the averaging jets inside `genForm`/`C` are the PER-COMPONENT jets of `ZLocJet` (r7: `fderiv` of the whole-torus
map, junk `0` if one component anywhere is not differentiable; r7 headline false, `compute/u_reads_omega0_20261012`); headline names `…6 → …8`.
 **r7 (F2, `statement_audit_r6_opus`)**: class and coverage are ONE hypothesis `ClassCoupled ell M c k S α₀ η U` (`ZR6A`) with ONE cube-factor binder `c`; the
 coupling theorem `ClassCoupled.plaq_gauge` / `ClassCoupled.plaqIn_gauge` and the consumers `CoercG8At.apply_gauge`, `P428Core8.apply_gauge` use it, so a
 `c`-class/`c+1`-coverage split is a type error in `ZR6A`, not a silent variation.
 The r5 coverage `CoversOm0c` (sites only) survives only in `ZT5D.proper_tower_hyps` (r5 form, kept as a control), the Mix variant `CoercG8AtMix` (range class,
 site coverage: NOT r6-faithful) and the legacy modules.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! ## conclusions at one point `(S, Λ, U)` -/

/-- the PRINTED claim at one point: `γ₀ ‖B̃‖² ≤ ⟨B, Δ_k B⟩` for `B = C B̃`, `B̃ ∈ Λ̃` supported on the touching bond set of `Λ`. -/
def InstIneq (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤
      GenP.genForm (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

/-- the r4 conclusion: invertibility (`WellDefG`) AND the inequality. -/
def InstAtWD (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  GenP.WellDefG (gparams ell k Lu hell S U a Lam) ∧ InstIneq ell k hell a Lu γ₀ S Lam U

/-- the inequality over the both-endpoint class (r2/r3 reading; weaker conclusion than `InstIneq`). -/
def InstIneqBoth (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambda Lam Bt →
    γ₀ * bondEnergy Bt ≤
      GenP.genForm (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

theorem InstAtWD.toHead {ell k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {γ₀ : ℝ}
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)}
    (h : InstAtWD ell k hell a Lu γ₀ S Lam U) : InstIneq ell k hell a Lu γ₀ S Lam U := h.2

theorem InstIneq.toBoth {ell k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {γ₀ : ℝ}
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)}
    (h : InstIneq ell k hell a Lu γ₀ S Lam U) : InstIneqBoth ell k hell a Lu γ₀ S Lam U :=
  fun Bt h1 h2 => h Bt h1 (OnLambda.toT h2)

/-! ## the inner claim at fixed `(k, Lu)`, cube factor `c`, class constant `α₀`, bound `γ₀` -/

/-- **the inner claim** (headline uses `c = 12`): torus tiling, admissible tower (`ℓ¹` distance, collar for every `k`), `Ω₀` covered by class cubes of
factor `c`, `Λ = B(Λ')` with the `RM` collar, `U` in the fixed-factor class `PerCubeRegular2 .. c ..`; conclusion `InstIneq`. -/
def CoercG8At (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

/-- the same with the r4 conclusion (`WellDefG` ∧ inequality). -/
def CoercG8AtWD (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstAtWD ell k hell a Lu γ₀ S Lam U

/-- the same with the r4 CLASS: cube factors `10 ≤ f ≤ F` all at once (`PerCubeRegularMix`, `CoversOm0`). -/
def CoercG8AtMix (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (F : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0 ell M F k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegularMix ell M F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

/-- the same over the both-endpoint class. -/
def CoercG8AtBoth (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqBoth ell k hell a Lu γ₀ S Lam U

theorem CoercG8AtWD.toHead {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8AtWD ell M R k hell a Lu c α₀ γ₀) :
    CoercG8At ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => (h hT S hS Lam hL U hU).toHead

theorem CoercG8At.toBoth {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8At ell M R k hell a Lu c α₀ γ₀) :
    CoercG8AtBoth ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => (h hT S hS Lam hL U hU).toBoth

/-! ## r7 (F2): the coupling theorem, used by the consumers of the inner claim -/

/-- the plaquettes of `plaqIn Ω₀` (the set `Δ`, `J` sum over) are covered by the SAME cube factor `c` that the class uses: `ClassCoupled` ⇒ one-`g` gauge
trivialisation of the four bonds with the class bound at factor `c`. -/
theorem _root_.AdalyFormal.StatementLane2.ClassCoupled.plaqIn_gauge {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U) :
    ∀ p ∈ plaqIn (S.Om 0), PlaqGaugeAt ell M c α₀ η U p :=
  fun p hp => h.plaq_gauge p hp

/-- **the inner claim, CONSUMED with its coupling**: applying `CoercG8At` at a point yields the printed inequality AND the plaquette gauge control at the same
cube factor `c` (the second conjunct is the content the class is for; it type-checks only if class and coverage share `c`). -/
theorem CoercG8At.apply_gauge {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8At ell M R k hell a Lu c α₀ γ₀) (hT : TorusOK ell M Lu)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {U : LinkCfg (scaleUp ell k Lu)} (hCU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    InstIneq ell k hell a Lu γ₀ S Lam U ∧
      ∀ p ∈ plaqIn (S.Om 0), PlaqGaugeAt ell M c α₀ ((ell : ℝ) ^ k)⁻¹ U p :=
  ⟨h hT S hS Lam hL U hCU, AdalyFormal.StatementLane2.ClassCoupled.plaqIn_gauge hCU⟩

theorem CoercG8AtWD.apply_gauge {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8AtWD ell M R k hell a Lu c α₀ γ₀) (hT : TorusOK ell M Lu)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {U : LinkCfg (scaleUp ell k Lu)} (hCU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    InstAtWD ell k hell a Lu γ₀ S Lam U ∧
      ∀ p ∈ plaqIn (S.Om 0), PlaqGaugeAt ell M c α₀ ((ell : ℝ) ^ k)⁻¹ U p :=
  ⟨h hT S hS Lam hL U hCU, AdalyFormal.StatementLane2.ClassCoupled.plaqIn_gauge hCU⟩

/-! ## the constants block and the printed side conditions -/

/-- `a₀`, `γ₀` (independent of `k ≥ 1, Lu, α₀, S, Λ, U, B̃`), cube factor `c`, smallness `c M α₀ ≤ a₀`. -/
def P428Core8At (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8At ell M R k hell a Lu c α₀ γ₀

/-- the headline constants block: `c = 12`. -/
def P428Core8 (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop := P428Core8At ell M R hell a 12

/-- pin (r5 (4) must-fire): the headline's cube factor is the number 12 (a definitional mutant `12 ↦ 10` makes this `rfl` fail). -/
theorem core6_is_c12 (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) :
    P428Core8 ell M R hell a = P428Core8At ell M R hell a 12 := rfl

/-- pin (r5 (2) must-fire): the headline ranges over `k ≥ 1` only (a mutant quantifying `k = 0` too, or a different range, makes this fail). -/
theorem core6_range (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) :
    P428Core8 ell M R hell a ↔ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
        CoercG8At ell M R k hell a Lu 12 α₀ γ₀ := Iff.rfl

def P428Core8WD (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtWD ell M R k hell a Lu 12 α₀ γ₀

theorem P428Core8WD.toHead {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : P428Core8WD ell M R hell a) :
    P428Core8 ell M R hell a := by
  obtain ⟨a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨a₀, ha, γ₀, hγ, fun k hk Lu α₀ h1 h2 => (h k hk Lu α₀ h1 h2).toHead⟩

/-- the printed side conditions: `ell ≥ 2`, `M = ell^m` with `m ≥ 1` (CMP99b p.408: "We take these numbers as powers of L"), `a > 0`.
(r4's `10 ≤ F` and `F + 2 ≤ R` are gone: `F` is replaced by the fixed `12`; the room condition was not printed and `R ≥ R₀` is existential.) -/
def SidePow6 (ell M : ℕ) (a : ℝ) : Prop :=
  2 ≤ ell ∧ (∃ m : ℕ, 1 ≤ m ∧ M = ell ^ m) ∧ 0 < a

/-- the weaker sufficient relation `ell ∣ M`. -/
def SideDvd6 (ell M : ℕ) (a : ℝ) : Prop := 2 ≤ ell ∧ 0 < M ∧ ell ∣ M ∧ 0 < a

theorem SidePow6.toDvd {ell M : ℕ} {a : ℝ} (h : SidePow6 ell M a) : SideDvd6 ell M a := by
  obtain ⟨h2, ⟨m, hm, hMm⟩, ha⟩ := h
  have hpos : 0 < ell ^ m := pow_pos (by omega) m
  exact ⟨h2, by rw [hMm]; exact hpos, by rw [hMm]; exact dvd_pow_self ell (by omega), ha⟩

/-- **the headline block CONSUMED with its coupling** (`c = 12`): the unfolded consequence of `P428Core8` in which the class hypothesis is the single
`ClassCoupled .. 12 ..` and the output includes the plaquette gauge control at the same factor 12. -/
def P428Core8Applied (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
        TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          InstIneq ell k hell a Lu γ₀ S Lam U ∧
            ∀ p ∈ plaqIn (S.Om 0), PlaqGaugeAt ell M 12 α₀ ((ell : ℝ) ^ k)⁻¹ U p

theorem P428Core8.apply_gauge {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : P428Core8 ell M R hell a) :
    P428Core8Applied ell M R hell a := by
  obtain ⟨a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨a₀, ha, γ₀, hγ, fun k hk Lu α₀ h1 h2 hT S hS Lam hL U hCU =>
    (h k hk Lu α₀ h1 h2).apply_gauge hT hS hL hCU⟩

/-- **`P428Genuine8`** (printed side condition `M = ell^m`) -/
def P428Genuine8 (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8 ell M R hell a

theorem P428Genuine8.apply_gauge {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : P428Genuine8 ell M R hell a) :
    P428Core8Applied ell M R hell a := h.2.apply_gauge

/-- variant: side condition `ell ∣ M` -/
def P428Genuine8Dvd (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SideDvd6 ell M a ∧ P428Core8 ell M R hell a

/-- variant: r4 conclusion with `WellDefG` -/
def P428Genuine8WD (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8WD ell M R hell a

/-- variant: `γ₀` may depend on the unit torus `Lu` (still not on `k`, `U`) -/
def P428Genuine8Print (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Lu : PeriodicLatticeExtent), ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
        CoercG8At ell M R k hell a Lu 12 α₀ γ₀

/-- variant: both-endpoint bond class -/
def P428Genuine8Both (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtBoth ell M R k hell a Lu 12 α₀ γ₀

/-- variant: the cube factor `c ≥ 10` is "a number ≥ 10" fixed FIRST (CMP99b p.396), `a₀, γ₀` may depend on it -/
def P428Genuine8AllC (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ ∀ c : ℕ, 10 ≤ c → P428Core8At ell M R hell a c

theorem P428Genuine8WD.toHead {ell M R : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine8WD ell M R hell a) : P428Genuine8 ell M R hell a := ⟨h.1, h.2.toHead⟩

theorem P428Genuine8.toDvd {ell M R : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine8 ell M R hell a) : P428Genuine8Dvd ell M R hell a := ⟨h.1.toDvd, h.2⟩

theorem P428Genuine8.toPrint {ell M R : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine8 ell M R hell a) : P428Genuine8Print ell M R hell a := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, fun Lu => ⟨γ₀, hγ, fun k hk α₀ h1 h2 => h k hk Lu α₀ h1 h2⟩⟩

theorem P428Genuine8.toBoth {ell M R : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine8 ell M R hell a) : P428Genuine8Both ell M R hell a := by
  obtain ⟨hp, a₀, ha, γ₀, hγ, h⟩ := h
  exact ⟨hp, a₀, ha, γ₀, hγ, fun k hk Lu α₀ h1 h2 => (h k hk Lu α₀ h1 h2).toBoth⟩

/-- `AllC` ⇒ headline: instantiate `c = 12`. -/
theorem P428Genuine8AllC.toHead {ell M R : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine8AllC ell M R hell a) : P428Genuine8 ell M R hell a :=
  ⟨h.1, h.2 12 (by norm_num)⟩

/-! ## the outer quantification -/

/-- **HEADLINE.**  (r7 reading note: the statement's operators `Δ`, `J` use the plaquette set `plaqIn Ω₀`, the lane's reading of p.394 — NOT printed wording; the claim that
this reading is the only one under which the statement is not false rests on PAPER arguments: the r5 collapse (single outward bond, `4 cos θ‖X‖²`; `statement_audit_r5_opus`)
and the concave-corner `(a + cos θ)‖X‖²` argument (`statement_audit_r6_opus` attack 2(b)) — neither is a Lean theorem.  ~~Likewise "Δ, Ginv read U only on class-constrained
bonds" is a paper argument (attack 1), not formalised.~~ [SUPERSEDED r8: that claim was FALSE for the r7 jets (`UR6.frozen_P428Target6_false`); for the r8
per-component jets it is a kernel theorem: `AdalyFormal.StatementLaneR8.genForm_congr_outside`, `InstIneq_congr`, `InstIneq_congr_class` (room `17·ell ≤ R·M`;
the `R D*` part `Tfull_congr` with room `2 ≤ R·M`).])  `ell ≥ 2` and `a > 0` fixed first; then thresholds `m₀` (for `M = ell^m`) and `R₀` (for `R`, which may depend on `m`); the
constants `a₀ = a₀(ell,M,R,a)` and `γ₀ = γ₀(ell,M,R,a)` are independent of `k ≥ 1`, the torus, `α₀`, the tower, `Λ`, `U`, `B̃` (p.428:
"a lower bound γ₀ > 0 independent of k and U").  `γ₀` MAY depend on `M, R` (the print names neither). -/
def P428Target8 : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8 ell (ell ^ m) R (by omega) a

/-- NAMED stronger variant (the freeze campaign's `LockA`): `a₀, γ₀` uniform in `M, R` beyond thresholds. -/
def P428Target8Unif : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8At ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀

theorem P428Target8Unif.toTarget (h : P428Target8Unif) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, fun m hm => ⟨R₁, fun R hR => ?_⟩⟩
  have hpos : 0 < ell ^ m := pow_pos (by omega) m
  refine ⟨⟨by omega, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 => ?_⟩
  exact hU m hm R hR k hk Lu α₀ h1 h2

/-- the strong reading: every printed-admissible parameter, no thresholds. -/
def P428Target8All : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (m : ℕ), 1 ≤ m → ∀ (R : ℕ), ∀ a : ℝ, 0 < a →
    P428Genuine8 ell (ell ^ m) R (by omega) a

theorem P428Target8All.toTarget (h : P428Target8All) : P428Target8 := by
  intro ell hell a ha
  exact ⟨1, le_rfl, fun m hm => ⟨0, fun R _ => h ell hell m hm R a ha⟩⟩

/-- the `K`-reading of p.408: `M = K M₀` (`M = K R₀ M₀`, `R₀, M₀` powers of `L` fixed by the proofs of [4], `K ≥ 1`), `ell ∣ M₀`. -/
def P428Target8K : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ell ∣ M₀ ∧ ∀ K : ℕ, 1 ≤ K → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8Dvd ell (K * M₀) R (by omega) a

/-- strongest reading with the sufficient side condition `ell ∣ M` (no thresholds) -/
def P428Target8AllDvd : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (M : ℕ), 0 < M → ell ∣ M → ∀ (R : ℕ), ∀ a : ℝ, 0 < a →
    P428Genuine8Dvd ell M R (by omega) a

theorem P428Target8AllDvd.toK (h : P428Target8AllDvd) : P428Target8K := by
  intro ell hell a ha
  refine ⟨ell, by omega, dvd_rfl, fun K hK => ⟨0, fun R _ => ?_⟩⟩
  exact h ell hell (K * ell) (Nat.mul_pos hK (by omega)) (dvd_mul_left ell K) R a ha

/-- the Dvd-all form, with the headline's `Core6`, implies the power-of-`ell` all-form -/
theorem P428Target8AllDvd.toAll (h : P428Target8AllDvd) : P428Target8All := by
  intro ell hell m hm R a ha
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have := h ell hell (ell ^ m) (pow_pos (by omega) m) hdvd R a ha
  exact ⟨⟨hell, ⟨m, hm, rfl⟩, ha⟩, this.2⟩

/-! ## the hypotheses, compared with the r4 class (S83: what each change EXCLUDES / ADDS) -/

/-- the fixed-factor regularity is implied by the range regularity when `12` lies in the range -/
theorem PerCubeRegularMix.toFix12 {L : PeriodicLatticeExtent} {ell M F k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (h : PerCubeRegularMix ell M F k S α₀ η U) (hF : 12 ≤ F) :
    PerCubeRegular2 ell M 12 k S α₀ η U := h 12 (by norm_num) hF

#print axioms core6_is_c12
#print axioms core6_range
#print axioms InstAtWD.toHead
#print axioms InstIneq.toBoth
#print axioms CoercG8AtWD.toHead
#print axioms CoercG8At.toBoth
#print axioms P428Core8WD.toHead
#print axioms SidePow6.toDvd
#print axioms P428Genuine8WD.toHead
#print axioms P428Genuine8.toDvd
#print axioms P428Genuine8.toPrint
#print axioms P428Genuine8.toBoth
#print axioms P428Genuine8AllC.toHead
#print axioms P428Target8Unif.toTarget
#print axioms P428Target8All.toTarget
#print axioms P428Target8AllDvd.toK
#print axioms P428Target8AllDvd.toAll
#print axioms PerCubeRegularMix.toFix12
#print axioms AdalyFormal.StatementLane2.ClassCoupled.plaqIn_gauge
#print axioms CoercG8At.apply_gauge
#print axioms CoercG8AtWD.apply_gauge
#print axioms P428Core8.apply_gauge
#print axioms P428Genuine8.apply_gauge

end AdalyFormal.StatementLaneG
