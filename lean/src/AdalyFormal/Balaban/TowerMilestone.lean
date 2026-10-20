import AdalyFormal.Balaban.VRestrictedRoute
import AdalyFormal.Balaban.TowerOneStep

/-!
# THE `k`-ITERATED COERCIVITY THEOREM AT THE su(2) LATTICE

`VRestrictedRoute.next_coercive_on_VSrc` proves ONE step: at a rung built on the flat lattice
operators, the coarse-side operator is `γ_V/q²`-coercive on CMP99b p.428's own subspace, with
`γ_V = 1/22522555753408512` free of the lattice extent. This module iterates it.

## §0 — WHAT IS PROVED

Two statements, both with a constant fixed BEFORE any lattice, depth or field is named.

* **`tower_uniform_coercive`** — for every extent `L`, every depth `k` with `2^(k+2) ∣ L μ + 1`,
  every level `j ≤ k` and every `u` on the level-`j` lattice whose level-`j` coarse datum lies in
  the source's subspace at the level-`(j+1)` lattice:

      γ* ‖u‖²  ≤  ⟨u, Δ_j u⟩ + ⟨u, P_Ax,j u⟩,        γ* = γ_V = 1/22522555753408512.

* **`tower_next_coercive_uniform`** — for the same data and every `B` in the source's subspace at
  the level-`(j+1)` lattice:

      8γ* ‖B‖²  ≤  ⟨B, Δ_{j+1} B⟩.

`Δ_0` is the lattice operator `Δ_k(1)`; `Δ_{j+1}` is the RG image `(Q G₁ Q*)⁻¹ − a·I` of `Δ_j`,
CMP99b (3.156) at `J = 0`, on the halved lattice's own bond carrier. `tower_law` /`towerAt_law`
are `rfl`: `op (j+1) = (rung j).next` is `TowerOneStep.Ladder`'s `law` on the nose.

**Neither constant decays with the depth.** There is no `q^{2j}`, no `gammaSeq`, and no tax: at
`U = 1` the (3.120) correction vanishes (`dpi = 0`), and the bound is re-derived at each level from
theorems that hold at EVERY periodic extent rather than transported through `q`.

## §1 — HOW IT WORKS, AND WHAT WAS MISSING BEFORE

`VRestrictedRoute` §6's three inputs are all extent-generic:
`ExtentUniformCoercivity.master_defect_bound_sharp` (`E ≤ 13264896·D + 6632448·P + 13583253568·C`),
`FibreAggregate.aggregate_fibre_bound_gamma` (`γ_agg = 1/3316224`) and the Stokes energy bound
`coarseCurlEnergy (Q v) ≤ ell⁻¹·curlEnergy v`. (`6632448` is quoted from that source theorem and is
asserted in NO statement of this module: `level_defect_bound` coarsens it UP to `13264896` so that
the two form terms carry one coefficient. That is a weakening, taken because it is what makes the
level-`j` bound read as `13264896·(⟨v,Δ_jv⟩ + P_Ax(v))`; the final `γ*` is unaffected because the
`P`-term enters the closing arithmetic only through `D + P`.) What is NOT extent-generic is that the first two
speak about the LATTICE curl energy, whereas at level `j ≥ 1` the operator is an RG image.

`Level` (§3) carries exactly the fact that closes that gap:

    hcurl :  curlEnergy_Λ(v)  ≤  ⟨v, Δ_Λ v⟩.

At level `0` it holds with equality (`OnRangeCoercivity.inner_deltaK_flat`). It is preserved by the
RG step (`stepLevel`) through the **lift identity** of §6,

    ⟨B, Δ_{k+1} B⟩ = ⟨u, Δ_k u⟩ + ⟨u, P_k u⟩,     u = G(Q*(S B)),  Q u = B,

combined with Stokes: `curlEnergy_{k+1}(B) ≤ ½·curlEnergy_k(u) ≤ ½·⟨u,Δ_k u⟩ ≤ ½·⟨B,Δ_{k+1}B⟩`. So
the invariant is reproduced with a factor `2` to spare and never degrades.

`TowerOneStep` §10b named "a bond-sector one-step averaging operator between two consecutive coarse
levels" as the object missing for a second rung. That was one obstruction and
`StridedAveraging.qStepCLM` now supplies it. The other — the one that actually blocks stacking, and
which §10b did not name — is that the level-`(k+1)` rung's `hinj`/`hMpos` are about the RG-IMAGE
operator, and no theorem in the tree said anything about ITS kernel. `Level.hcurl` closes that:
`level_defect_bound` reads the master defect bound at the level's own operator, and
`level_fine_pos` turns it into positive definiteness of `M` with no whole-space coercivity anywhere.

This module takes the transport route rather than the strided one: level `k+1` lives on
`BondFnL2 (coarseExtent^k L 2)` via `VRestrictedRoute` §1's reindexing promoted to a
`LinearIsometryEquiv` (`coarseIso`). That is what returns the carrier to BOND shape so a second
rung can be stacked at all.

## §2 — SCOPE, STATED

1. **`U = 1` ONLY.** Every operator here is at `trivialU`: `Δ_0 = deltaKCLMNormalized (trivialU L)`,
   `Q = qCLM (trivialU ·) 2`, and the (3.120) correction is taken to be `0` — which at `U = 1` is
   not an assumption but the fact `TowerOneStep.Rung.nextPi_coercive_gf_at_zero` is stated for. The
   curved tower is a separate construction and is NOT claimed here.
2. **`J = 0`.** `Rung.next` is (3.156) at vanishing current; the `J`-term is not modelled.
3. **V-RESTRICTED.** The bound is on CMP99b p.428's own subspace, not the whole space. That is the
   source's restriction, not a weakening chosen here — and `vLat_is_load_bearing` re-exports
   `VRestrictedRoute`'s control showing the whole-space statement is FALSE at the lattice.
4. **THE DEPTH IS BOUNDED, AND THAT IS NOT A GAP — IT IS THE LATTICE.** `TowerOneStep.Ladder`
   demands a rung at EVERY `k : ℕ`. On a finite torus the extent tower terminates:
   `levelExtent_spec` gives `levelExtent L k μ + 1 = (L μ + 1)/2^k`, which reaches `1`, and there
   `LevelOK` fails (`witL_level_three_not_ok` exhibits it). So no total `Ladder` over the su(2)
   lattice exists, and this module produces the depth-bounded chain instead of inhabiting `Ladder`
   the way `TowerOneStep` §3 item 2 warns is possible (trivial carriers).
5. **TWO ADJUDICATIONS ARE INHERITED, NOT PROVED HERE.** (a) that `pAxCLM` at a level's own lattice
   is (3.128)'s gauge-fixing form there — inherited from `AxialCoercivity` and
   `OnRangeCoercivity.honestLatticeRung`; (b) that p.428's `Q₁` is read as the lattice's own
   averaging one level up — inherited from `VRestrictedRoute`'s §0 scope note. Both are conventions
   fixed at level `0` and used unchanged at every level; this module introduces no third reading.
6. **WHAT THIS IS NOT.** It is not p.428's full uniformity statement: that is about the curved
   tower with `J ≠ 0` and the `k`-uniform control of the whole (3.128) apparatus. What is
   established here is the coercivity leg, at `U = 1`, uniformly in the depth.

## §3 — BINDER AUDIT (against the `TowerUniformSuTwo` failure)

The registry records `TowerUniformSuTwo` inhabited by a content-free term: `V := ⊥` emptied the
subspace and a constant `Uof` collapsed the `∀U`. Every binder here is audited in
`compute/tower_milestone/PROGRESS.md` §4; the two structural guards are:

* **the domain family is PINNED, not free** — `VLat Λ` is a definition with the source's three
  clauses at the lattice `Λ`, and `vLat_nontrivial` exhibits a NONZERO element of it at every
  admissible level (transported from `VRestrictedRoute`'s named witness field). `milestone_nonvacuous`
  puts BOTH sides of the conclusion strictly positive there;
* **the `j`-index genuinely varies** — the carriers are `BondFnL2 (levelExtent L j)`, whose lattice
  shrinks by a factor `2` per side per level (`witL_extents`: `15 → 7 → 3`), and `op (j+1)` is
  pinned by an EQUATION to the RG image of `op j`, not supplied as free data.

## §3a — EVERY HEADLINE `∀`-THEOREM CARRIES A WITNESS FOR **ITS OWN** HYPOTHESIS

⚠ **This section exists because the earlier version of this module did not have it, and that was
CONVICTED** (`compute/milestone_prosecution/VERDICT.md`, item A). At commit `5dfe7f6d` the module's
entire nonvacuity apparatus — `vLat_nontrivial`, `vLat_carrier_nontrivial`, `milestone_nonvacuous`,
`depth_one_nonvacuous`, `depth_two_nonvacuous`, and all six S91 rows — instantiated only the
COARSE-side hypothesis `VLat Λ_{j+1} B`. The FINE-side headline `tower_uniform_coercive`, whose
hypothesis is the DERIVED predicate `VLat Λ_{j+1} (qLevel u)`, was never instantiated at any `u` at
all: the module never checked that its own first-listed theorem says anything about a nonzero
vector.

**Why no gate caught it, and what the control is.** `formal/tools/s91_targets.py` enumerates
declarations whose CONCLUSION is headed by an existential — `Exists`, and existentials in disguise
such as `Function.Surjective` (measured: it reports `qLevel_surjective` below on that head).
Hypothesis-domain vacuity inside a `∀`-theorem is invisible to it:
the statement `∀ u, H u → C u` is a theorem about `{0}` whenever `H` is satisfied only by `0`, and
nothing in its syntax is an `∃`. This is the `TowerUniformSuTwo` failure mode (`V := ⊥`) relocated
out of the statement's free data and into a derived predicate several definitions downstream, where
the `∃`-detector cannot see it. The kernel cannot see it either — the proof is correct in both
cases. The only control is a per-theorem one, and it is now discharged PER HEADLINE THEOREM, not
per module:

| headline `∀`-theorem | hypothesis witnessed | witness declaration |
| --- | --- | --- |
| `tower_uniform_coercive` | `VLat Λ_{j+1} (ofLp (qLevel u))` | `tower_uniform_nonvacuous`, and at the closed numeral lattice `witL`: `tower_uniform_depth_zero_nonvacuous` (`j = 0`), `tower_uniform_depth_one_nonvacuous` (`j = 1`) |
| `tower_next_coercive` | `VLat Λ_{j+1} (ofLp B)` | `milestone_nonvacuous`, `depth_one_nonvacuous`, `depth_two_nonvacuous` |
| `tower_next_coercive_uniform` | `VLat Λ_{j+1} (ofLp B)` | `tower_next_uniform_nonvacuous`, `tower_next_uniform_depth_two_nonvacuous` |

Each witness exhibits a NONZERO element of its theorem's own hypothesis domain and puts BOTH sides
of THAT theorem's conclusion strictly positive, the right-hand side by applying the headline theorem
itself rather than re-deriving a look-alike. The fine-side witness is not assumed: `qLevel` is
surjective (`qLevel_surjective`, §5, from the generic `BridgeInverse.qCLM_surjective_trivialU`
composed with the isometric equivalence `coarseIso`), so the coarse witness pulls back, and
linearity forces the preimage to be nonzero.

⚠ **`u ≠ 0` IS NOT ENOUGH ON THE FINE SIDE.** `VLat Λ 0` is TRUE, so the fine hypothesis
`VLat Λ_{j+1} (qLevel u)` is satisfied by every element of `ker qLevel` no matter what the subspace
contains — a witness taken from that kernel would exhibit only that `Q` has a kernel. The fine-side
witnesses therefore carry the extra conjunct `qLevel u ≠ 0`, so the certified point is one whose
COARSE DATUM is a nonzero element of the subspace. `level_gf_on_preimage_nonvacuous` states the
same at an ARBITRARY `Level Λ` and an arbitrary `4`-divisible lattice, so the nonemptiness is not an
artifact of the particular operators the tower builds.

**MEASURED must-fire (`compute/milestone_repair/mutants/`).** Mutation `MUT-E` adds the conjunct
`u = 0` to `tower_uniform_coercive`'s hypothesis, emptying its domain to `{0}` while leaving the
theorem provable. Against the module AS IT STANDS the compile FAILS, at
`tower_uniform_nonvacuous`'s application of the headline. Against the module as it stood at the
prosecuted commit `5dfe7f6d` the same mutation compiles CLEAN — exit 0, 75/75 `#print axioms`, no
error: the pre-repair nonvacuity apparatus could not detect the emptying of the theorem it was
supposed to be certifying. That measurement is what this section is for.
-/
namespace AdalyFormal.Balaban.TowerMilestone

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2 qCLM qstarCLM fineCLM fineCLM_inner)
open AdalyFormal.Balaban.U1AnchorCoarse (coarseExtent coarseExtent_spec)
open AdalyFormal.Balaban.VRestrictedRoute (cbEquiv pullS coarseCurlEnergy curlEnergy_pullS
  coarseCurlEnergy_Q_le gammaV gammaV_pos)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAxCLM pAx_nonneg pAxCLM_pos pAxCLM_symm
  inner_pAxCLM_eq' pAx_eq_zero_of_vanishing_on_Ax)
open AdalyFormal.Balaban.AxialContour (Ax)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized deltaKCLMNormalized_symm)
open AdalyFormal.Balaban.OnRangeCoercivity (inner_deltaK_flat norm_sq_eq_bondEnergy
  injective_of_pos_definite)
open AdalyFormal.Balaban.ExtentUniformCoercivity (master_defect_bound_sharp coarseEnergy
  norm_sq_qCLM)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.TowerOneStep (Rung piOp piOp_zero)

variable {L Λ : PeriodicLatticeExtent}

/-! ## §1 — THE EXTENT TOWER -/

/-- The lattice at level `k`: halve every side, `k` times. -/
def levelExtent (L : PeriodicLatticeExtent) : ℕ → PeriodicLatticeExtent
  | 0 => L
  | (k + 1) => coarseExtent (levelExtent L k) 2

@[simp] theorem levelExtent_zero : levelExtent L 0 = L := rfl

@[simp] theorem levelExtent_succ (k : ℕ) :
    levelExtent L (k + 1) = coarseExtent (levelExtent L k) 2 := rfl

/-- **THE EXTENT COUNT.** If every side of `L` is `2^n`-divisible, the level-`n` side is exactly
`(L μ + 1) / 2^n`. Stated multiplicatively so no `Nat` division appears. -/
theorem levelExtent_spec : ∀ (n : ℕ) (_ : ∀ μ : Fin 3, (2 : ℕ) ^ n ∣ (L μ + 1)) (μ : Fin 3),
    2 ^ n * (levelExtent L n μ + 1) = L μ + 1 := by
  intro n
  induction n with
  | zero => intro _ μ; simp
  | succ m ih =>
      intro hpow μ
      have hm : ∀ ν : Fin 3, (2 : ℕ) ^ m ∣ (L ν + 1) := fun ν =>
        dvd_trans (pow_dvd_pow 2 (Nat.le_succ m)) (hpow ν)
      have hstep := ih hm μ
      -- `2 ∣ levelExtent L m μ + 1`
      have h2 : (2 : ℕ) ∣ (levelExtent L m μ + 1) := by
        obtain ⟨c, hc⟩ := hpow μ
        have : 2 ^ m * (levelExtent L m μ + 1) = 2 ^ m * (2 * c) := by
          rw [hstep, hc]; ring
        have hcan := Nat.eq_of_mul_eq_mul_left ((Nat.two_pow_pos m)) this
        exact ⟨c, hcan⟩
      have hcs := coarseExtent_spec (L := levelExtent L m) (ell := 2) (by norm_num)
        (fun ν => by
          obtain ⟨c, hc⟩ := hpow ν
          have hstepν := ih hm ν
          have : 2 ^ m * (levelExtent L m ν + 1) = 2 ^ m * (2 * c) := by
            rw [hstepν, hc]; ring
          exact ⟨c, Nat.eq_of_mul_eq_mul_left ((Nat.two_pow_pos m)) this⟩) μ
      calc 2 ^ (m + 1) * (levelExtent L (m + 1) μ + 1)
          = 2 ^ m * (2 * (coarseExtent (levelExtent L m) 2 μ + 1)) := by
            rw [levelExtent_succ]; ring
        _ = 2 ^ m * (levelExtent L m μ + 1) := by rw [hcs]
        _ = L μ + 1 := hstep

/-- The level-`j` side is `2^(n-j)`-divisible whenever `L`'s is `2^n`-divisible and `j ≤ n`. -/
theorem levelExtent_dvd {n : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ n ∣ (L μ + 1))
    {j : ℕ} (hj : j ≤ n) (μ : Fin 3) : (2 : ℕ) ^ (n - j) ∣ (levelExtent L j μ + 1) := by
  have hj' : ∀ ν : Fin 3, (2 : ℕ) ^ j ∣ (L ν + 1) := fun ν =>
    dvd_trans (pow_dvd_pow 2 hj) (hpow ν)
  have hspec := levelExtent_spec j hj' μ
  obtain ⟨c, hc⟩ := hpow μ
  have hsplit : (2 : ℕ) ^ n = 2 ^ j * 2 ^ (n - j) := by
    rw [← pow_add]; congr 1; omega
  have : 2 ^ j * (levelExtent L j μ + 1) = 2 ^ j * (2 ^ (n - j) * c) := by
    rw [hspec, hc, hsplit]; ring
  exact ⟨c, Nat.eq_of_mul_eq_mul_left ((Nat.two_pow_pos j)) this⟩

/-- **THE ADMISSIBILITY PREDICATE.** The two lattice conditions every rung at level `j` needs:
the side is even (so the level-`j` blocking is defined) and at least two blocks wide (so the
block does not wrap). Both are consequences of `4 ∣ side`. -/
def LevelOK (L : PeriodicLatticeExtent) (j : ℕ) : Prop :=
  (∀ μ : Fin 3, (2 : ℕ) ∣ (levelExtent L j μ + 1))
    ∧ (∀ μ : Fin 3, 2 * 2 ≤ levelExtent L j μ + 1)

/-- **`2^(k+2) ∣ L μ + 1` MAKES LEVELS `0 … k` ADMISSIBLE.** This is the extent condition the
depth-`k` tower needs, and it is exactly the `4 ∣ L μ + 1` of `VRestrictedRoute` at `k = 0`. -/
theorem levelOK_of_pow {k : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1))
    {j : ℕ} (hj : j ≤ k) : LevelOK L j := by
  have hfour : ∀ μ : Fin 3, (4 : ℕ) ∣ (levelExtent L j μ + 1) := by
    intro μ
    have h := levelExtent_dvd hpow (j := j) (by omega) μ
    have hle : (2 : ℕ) ^ 2 ∣ 2 ^ (k + 2 - j) := pow_dvd_pow 2 (by omega)
    exact dvd_trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2) (dvd_trans hle h)
  refine ⟨fun μ => dvd_trans (by norm_num) (hfour μ), fun μ => ?_⟩
  obtain ⟨c, hc⟩ := hfour μ
  omega


/-! ## §2 — `VLat`: CMP99b p.428's SUBSPACE, AT AN ARBITRARY LATTICE

`VRestrictedRoute.VSrc` states the source's three clauses about a *coarse* field `B` of `L` at
scale `2`, but it states every one of them through the pullback `pullC` — i.e. entirely in terms of
the bond field `pullS B` on the coarse lattice **regarded as a lattice in its own right**. So the
predicate is intrinsic to that lattice, and `VLat` below is exactly `VSrc` read there. Clause (c1)
is `True` on a torus (`Λᶜ = ∅`) and is carried explicitly, as in `VSrc`, so the clause count still
matches the source. -/

/-- **THE SOURCE'S SUBSPACE AT THE LATTICE `Λ`.** `{A : A = 0 on Λᶜ, A = 0 on ⋃_{y} Ax(y),
Q A = 0}`, with `Q` the lattice's own scale-`2` averaging. -/
def VLat (Λ : PeriodicLatticeExtent) (A : Bond Λ → SuTwo) : Prop :=
  True
  ∧ (∀ y ∈ CoarseLattice Λ 2, ∀ b ∈ Ax y 2, A b = 0)
  ∧ (∀ c : CoarseBond Λ 2, lineCoarseRestrictCov (trivialU Λ) 2 A c = 0)

/-- **`VLat` IS `VSrc`, TRANSPORTED.** At level `0` the two predicates are the same statement:
`VSrc hdvd4 B` is `VLat (coarseExtent L 2) (pullS B)`. Definitional; recorded so the reader can see
that this module is not inventing a new subspace. -/
theorem vLat_eq_vSrc (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (B : CoarseBond L 2 → SuTwo) :
    AdalyFormal.Balaban.VRestrictedRoute.VSrc hdvd4 B
      ↔ VLat (coarseExtent L 2) (pullS (by norm_num)
          (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) B) := Iff.rfl

/-- The coarse fibre bound, at any even lattice, on `VLat`: `γ_agg‖A‖² ≤ curlEnergy A`.
`FibreAggregate.aggregate_fibre_bound_gamma` with clause (c3) as its hypothesis and clause (c2)
killing its `pAx` term. This is `VRestrictedRoute.coarse_fibre_bound_on_VSrc` stated at the lattice
where it lives rather than through the pullback. -/
theorem fibre_bound_on_VLat (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    {A : Bond Λ → SuTwo} (hA : VLat Λ A) :
    AdalyFormal.Balaban.FibreAggregate.gammaAgg * bondEnergy A ≤ curlEnergy A := by
  obtain ⟨-, hc2, hc3⟩ := hA
  have hfib := AdalyFormal.Balaban.FibreAggregate.aggregate_fibre_bound_gamma hdvd A hc3
  rw [AdalyFormal.Balaban.FibreCoercivity.deltaK_trivialU_eq_curlEnergy] at hfib
  rw [pAx_eq_zero_of_vanishing_on_Ax A _ _ hc2, add_zero] at hfib
  exact hfib

/-! ## §3 — A LEVEL: an operator carrying the one invariant the tower needs

`Level Λ` bundles the level's operator with exactly two facts: it is symmetric, and it dominates
the lattice's own curl energy. The second is the whole content — it is what lets the level-`Λ`
master defect bound (a theorem at EVERY periodic extent) be read at the RG-image operator, and it
is preserved by the RG step with a factor to spare. -/

/-- The data carried from level to level. -/
structure Level (Λ : PeriodicLatticeExtent) where
  /-- The level's operator. -/
  op : BondFnL2 Λ →L[ℝ] BondFnL2 Λ
  /-- Symmetry. -/
  hsym : ∀ u v : BondFnL2 Λ, (inner ℝ u (op v) : ℝ) = (inner ℝ (op u) v : ℝ)
  /-- **THE INVARIANT.** The quadratic form dominates the lattice curl energy. -/
  hcurl : ∀ v : BondFnL2 Λ, curlEnergy (WithLp.ofLp v) ≤ (inner ℝ v (op v) : ℝ)

/-- The invariant forces positive semidefiniteness. -/
theorem Level.hpsd (lvl : Level Λ) (v : BondFnL2 Λ) : (0 : ℝ) ≤ (inner ℝ v (lvl.op v) : ℝ) :=
  le_trans (curlEnergy_nonneg _) (lvl.hcurl v)

/-- **LEVEL 0: THE LATTICE OPERATOR ITSELF.** `Δ_k(1)` is symmetric and its quadratic form IS the
curl energy, so the invariant holds with equality. -/
noncomputable def baseLevel (Λ : PeriodicLatticeExtent) : Level Λ where
  op := deltaKCLMNormalized (trivialU Λ)
  hsym := fun u v => (deltaKCLMNormalized_symm (trivialU Λ) u v).symm
  hcurl := fun v => le_of_eq (inner_deltaK_flat v).symm

@[simp] theorem baseLevel_op (Λ : PeriodicLatticeExtent) :
    (baseLevel Λ).op = deltaKCLMNormalized (trivialU Λ) := rfl

/-! ## §4 — THE LEVEL-`Λ` DEFECT BOUND, AT THE LEVEL'S OWN OPERATOR

`ExtentUniformCoercivity.master_defect_bound_sharp` holds at every even extent, about the LATTICE
curl energy. `Level.hcurl` converts it into a statement about the level's operator, with the same
explicit `L`-free constants. This is what supplies `hinj`/`hMpos` at every level, not only at
level `0`. -/

/-- **THE DEFECT BOUND AT LEVEL `Λ`.** `‖v‖² ≤ 13264896·(⟨v,Δv⟩ + P_Ax(v)) + 13583253568·‖Qv‖²`. -/
theorem level_defect_bound (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (v : BondFnL2 Λ) :
    ‖v‖ ^ 2 ≤ 13264896 * ((inner ℝ v (lvl.op v) : ℝ)
        + (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ))
      + 13583253568 * ‖qCLM (trivialU Λ) 2 v‖ ^ 2 := by
  have hm := master_defect_bound_sharp hdvd (WithLp.ofLp v)
  have hcurl := lvl.hcurl v
  have hP : (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ)
      = pAx (WithLp.ofLp v) (CoarseLattice Λ 2) 2 := inner_pAxCLM_eq' _ _ v
  have hPnn : (0 : ℝ) ≤ pAx (WithLp.ofLp v) (CoarseLattice Λ 2) 2 := pAx_nonneg _ _ _
  have hQ : ‖qCLM (trivialU Λ) 2 v‖ ^ 2
      = coarseEnergy (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp v)) := norm_sq_qCLM v
  have hn : ‖v‖ ^ 2 = bondEnergy (WithLp.ofLp v) := norm_sq_eq_bondEnergy v
  rw [hn, hP, hQ]
  nlinarith [hm, hcurl, hPnn]

/-- **POSITIVE DEFINITENESS OF `M` AT LEVEL `Λ`** — the rung's `hMpos`/`hinj`, at the level's own
operator, from the defect bound. No whole-space coercivity is used: the three nonnegative terms
cannot all vanish on a nonzero vector, because the defect bound would then force `‖v‖² ≤ 0`.

The `K`-side is left abstract and tied to the lattice `Q` only through `hQnorm`, so the same
theorem serves the rung whose codomain is the coarse carrier and the rung whose codomain is the
next lattice's bond carrier. -/
theorem level_fine_pos {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) {a : ℝ} (ha : 0 < a)
    (Q : BondFnL2 Λ →L[ℝ] K) (Qstar : K →L[ℝ] BondFnL2 Λ)
    (hadj : ∀ (x : BondFnL2 Λ) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hQnorm : ∀ x : BondFnL2 Λ, ‖Q x‖ = ‖qCLM (trivialU Λ) 2 x‖)
    (v : BondFnL2 Λ) (hv : v ≠ 0) :
    (0 : ℝ) < (inner ℝ v
      (fineCLM (piOp lvl.op 0) (pAxCLM (CoarseLattice Λ 2) 2) Q Qstar a v) : ℝ) := by
  rw [fineCLM_inner _ _ _ _ _ hadj v]
  have hpi : (inner ℝ v (piOp lvl.op 0 v) : ℝ) = (inner ℝ v (lvl.op v) : ℝ) := by
    simp [piOp]
  rw [hpi, hQnorm v]
  set D : ℝ := (inner ℝ v (lvl.op v) : ℝ) with hD
  set P : ℝ := (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ) with hP
  set Z : ℝ := ‖qCLM (trivialU Λ) 2 v‖ ^ 2 with hZ
  have hDnn : (0 : ℝ) ≤ D := lvl.hpsd v
  have hPnn : (0 : ℝ) ≤ P := pAxCLM_pos _ _ v
  have hZnn : (0 : ℝ) ≤ Z := sq_nonneg _
  have hvn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  have hdef : ‖v‖ ^ 2 ≤ 13264896 * (D + P) + 13583253568 * Z := level_defect_bound lvl hdvd v
  by_contra hcon
  simp only [not_lt] at hcon
  have haZ : (0 : ℝ) ≤ a * Z := mul_nonneg ha.le hZnn
  have hDP : D + P = 0 := by linarith
  have haZ0 : a * Z = 0 := by linarith
  have hZ0 : Z = 0 := by
    rcases mul_eq_zero.1 haZ0 with h | h
    · exact absurd h (ne_of_gt ha)
    · exact h
  rw [hDP, hZ0] at hdef
  linarith

/-! ## §5 — THE TRANSPORT, AND THE RUNG BETWEEN TWO CONSECUTIVE LATTICES

`VRestrictedRoute` §1 built the index equivalence `CoarseBond Λ 2 ≃ Bond (coarseExtent Λ 2)`; on
the `ℓ²` carriers it induces a LINEAR ISOMETRY, which is what makes the level-`(k+1)` carrier a
BOND carrier again rather than a coarse one. That is the only reason a second rung can be stacked
on a first: without it the rung's codomain type never returns to the shape its domain had. -/

/-- **THE CARRIER TRANSPORT.** `Mathlib`'s `piLpCongrLeft` on §1's index equivalence. -/
noncomputable def coarseIso (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    CoarseFnL2 Λ 2 ≃ₗᵢ[ℝ] BondFnL2 (coarseExtent Λ 2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (cbEquiv (by norm_num) hdvd)

/-- The transport IS `VRestrictedRoute.pullS` — definitional, so nothing is smuggled in. -/
theorem coarseIso_ofLp (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (F : CoarseFnL2 Λ 2) :
    WithLp.ofLp (coarseIso hdvd F) = pullS (by norm_num) hdvd (WithLp.ofLp F) := rfl

/-- **THE LEVEL-`Λ` AVERAGING, LANDING ON THE NEXT LATTICE'S BOND CARRIER.** -/
noncomputable def qLevel (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    BondFnL2 Λ →L[ℝ] BondFnL2 (coarseExtent Λ 2) :=
  (coarseIso hdvd).toLinearIsometry.toContinuousLinearMap.comp (qCLM (trivialU Λ) 2)

/-- Its adjoint. -/
noncomputable def qLevelStar (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    BondFnL2 (coarseExtent Λ 2) →L[ℝ] BondFnL2 Λ :=
  (qstarCLM (trivialU Λ) 2).comp
    (coarseIso hdvd).symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem qLevel_apply (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (x : BondFnL2 Λ) :
    qLevel hdvd x = coarseIso hdvd (qCLM (trivialU Λ) 2 x) := rfl

@[simp] theorem qLevelStar_apply (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (B : BondFnL2 (coarseExtent Λ 2)) :
    qLevelStar hdvd B = qstarCLM (trivialU Λ) 2 ((coarseIso hdvd).symm B) := rfl

theorem norm_qLevel (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (x : BondFnL2 Λ) :
    ‖qLevel hdvd x‖ = ‖qCLM (trivialU Λ) 2 x‖ := by
  rw [qLevel_apply]
  exact (coarseIso hdvd).norm_map _

theorem qLevel_hadj (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (x : BondFnL2 Λ) (B : BondFnL2 (coarseExtent Λ 2)) :
    (inner ℝ (qLevelStar hdvd B) x : ℝ) = (inner ℝ B (qLevel hdvd x) : ℝ) := by
  rw [qLevelStar_apply, qLevel_apply,
    AdalyFormal.Balaban.BridgeInverse.qCLM_hadj (trivialU Λ) 2 x ((coarseIso hdvd).symm B)]
  rw [show (inner ℝ B (coarseIso hdvd (qCLM (trivialU Λ) 2 x)) : ℝ)
      = (inner ℝ (coarseIso hdvd ((coarseIso hdvd).symm B))
          (coarseIso hdvd (qCLM (trivialU Λ) 2 x)) : ℝ) by
    rw [LinearIsometryEquiv.apply_symm_apply]]
  exact ((coarseIso hdvd).inner_map_map _ _).symm

theorem qLevelStar_injective (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    Function.Injective (qLevelStar hdvd) := by
  intro B C h
  have h1 : qstarCLM (trivialU Λ) 2 ((coarseIso hdvd).symm B)
      = qstarCLM (trivialU Λ) 2 ((coarseIso hdvd).symm C) := h
  have h2 := AdalyFormal.Balaban.BridgeInverse.qstar_injective_of_surjective
    (qCLM (trivialU Λ) 2) (qstarCLM (trivialU Λ) 2)
    (AdalyFormal.Balaban.BridgeInverse.qCLM_hadj (trivialU Λ) 2)
    (AdalyFormal.Balaban.BridgeInverse.qCLM_surjective_trivialU (by norm_num) hdvd) h1
  exact (coarseIso hdvd).symm.injective h2

/-- **THE LEVEL AVERAGING IS ONTO THE NEXT LATTICE'S BOND CARRIER.** `qLevel` is `coarseIso ∘ qCLM`,
a bijection after a surjection: `BridgeInverse.qCLM_surjective_trivialU` is generic (no smallness,
no level restriction, only `0 < 2` and the divisibility this module already carries), and `coarseIso`
is a `LinearIsometryEquiv`. Stated separately because it is the fact that turns a witness for the
COARSE-side subspace into a witness for the FINE-side hypothesis `qLevel u ∈ VLat` (§11), and it is
reusable at any level (LAW-19). -/
theorem qLevel_surjective (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) :
    Function.Surjective (qLevel hdvd) := by
  intro B
  obtain ⟨F, hF⟩ := (coarseIso hdvd).surjective B
  obtain ⟨u, hu⟩ :=
    AdalyFormal.Balaban.BridgeInverse.qCLM_surjective_trivialU (by norm_num) hdvd F
  exact ⟨u, by rw [qLevel_apply, hu, hF]⟩

/-- **THE LEVEL-`Λ` RUNG.** Domain: the level-`Λ` bond carrier. Codomain: the NEXT lattice's bond
carrier. Index operator: the level's own operator, `π`-extended at a vanishing correction
(`U = 1`, where `Δ′_π` is zero — `TowerOneStep.piCorrectionBound_zero`).

Every field is a theorem: `hadj`, `hQ`, `hq`, `hQstarInj` from the tree's `Q`-side facts,
`hDsym` from `Level.hsym`, `hPsym`/`hPpos` from `AxialCoercivity`, and `hinj`/`hMpos` from
`level_fine_pos` — i.e. from the LEVEL-`Λ` DEFECT BOUND, not from a whole-space hypothesis. -/
noncomputable def levelRung (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) {a : ℝ} (ha : 0 < a) :
    Rung (BondFnL2 Λ) (BondFnL2 (coarseExtent Λ 2)) (piOp lvl.op 0) where
  Q := qLevel hdvd
  Qstar := qLevelStar hdvd
  P := pAxCLM (CoarseLattice Λ 2) 2
  a := a
  q := ‖qCLM (trivialU Λ) 2‖
  hadj := qLevel_hadj hdvd
  ha := ha.le
  hq := AdalyFormal.Balaban.BridgeInverse.qCLM_norm_pos (by norm_num) hdvd hwide _
  hQ := fun x => by
    rw [norm_qLevel hdvd x]
    exact AdalyFormal.Balaban.BridgeInverse.qCLM_le (trivialU Λ) 2 x
  hDsym := fun u v => by simpa [piOp] using lvl.hsym u v
  hPsym := pAxCLM_symm (CoarseLattice Λ 2) 2
  hPpos := pAxCLM_pos (CoarseLattice Λ 2) 2
  hinj := injective_of_pos_definite _
    (fun x hx => level_fine_pos lvl hdvd ha _ _ (qLevel_hadj hdvd) (norm_qLevel hdvd) x hx)
  hMpos := fun x hx =>
    level_fine_pos lvl hdvd ha _ _ (qLevel_hadj hdvd) (norm_qLevel hdvd) x hx
  hQstarInj := qLevelStar_injective hdvd


/-! ## §6 — TWO FACTS ABOUT ANY RUNG THAT THE TOWER NEEDS

Neither is in `TowerOneStep`; both are proved here from that module's own primitives, and both are
about an ARBITRARY rung, so they are reusable (LAW-19). -/

section RungFacts

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K] {Δ : H →L[ℝ] H}

/-- `G₁ = M⁻¹` is symmetric, because `M` is. -/
theorem rung_G_sym (r : Rung H K Δ) (u v : H) :
    (inner ℝ u (r.G v) : ℝ) = (inner ℝ (r.G u) v : ℝ) := by
  have hu : r.M (r.G u) = u := r.M_G_right u
  have hv : r.M (r.G v) = v := r.M_G_right v
  calc (inner ℝ u (r.G v) : ℝ) = (inner ℝ (r.M (r.G u)) (r.G v) : ℝ) := by rw [hu]
    _ = (inner ℝ (r.G u) (r.M (r.G v)) : ℝ) := (r.M_sym (r.G u) (r.G v)).symm
    _ = (inner ℝ (r.G u) v : ℝ) := by rw [hv]

/-- `T = Q G Q*` is symmetric. -/
theorem rung_T_sym (r : Rung H K Δ) (B C : K) :
    (inner ℝ B (r.T C) : ℝ) = (inner ℝ (r.T B) C : ℝ) := by
  have h1 : (inner ℝ B (r.T C) : ℝ) = (inner ℝ (r.Qstar B) (r.G (r.Qstar C)) : ℝ) := by
    rw [r.T_apply, r.hadj (r.G (r.Qstar C)) B]
  have h2 : (inner ℝ (r.Qstar B) (r.G (r.Qstar C)) : ℝ)
      = (inner ℝ (r.G (r.Qstar B)) (r.Qstar C) : ℝ) := rung_G_sym r _ _
  have h3 : (inner ℝ (r.G (r.Qstar B)) (r.Qstar C) : ℝ) = (inner ℝ (r.T B) C : ℝ) := by
    have hcomm := r.hadj (r.G (r.Qstar B)) C
    calc (inner ℝ (r.G (r.Qstar B)) (r.Qstar C) : ℝ)
        = (inner ℝ (r.Qstar C) (r.G (r.Qstar B)) : ℝ) := real_inner_comm _ _
      _ = (inner ℝ C (r.Q (r.G (r.Qstar B))) : ℝ) := hcomm
      _ = (inner ℝ (r.T B) C : ℝ) := real_inner_comm _ _
  rw [h1, h2, h3]

/-- `S = T⁻¹` is symmetric. -/
theorem rung_S_sym (r : Rung H K Δ) (B C : K) :
    (inner ℝ B (r.S C) : ℝ) = (inner ℝ (r.S B) C : ℝ) := by
  have hB : r.T (r.S B) = B := r.T_S B
  have hC : r.T (r.S C) = C := r.T_S C
  calc (inner ℝ B (r.S C) : ℝ) = (inner ℝ (r.T (r.S B)) (r.S C) : ℝ) := by rw [hB]
    _ = (inner ℝ (r.S B) (r.T (r.S C)) : ℝ) := (rung_T_sym r (r.S B) (r.S C)).symm
    _ = (inner ℝ (r.S B) C : ℝ) := by rw [hC]

/-- **THE RG IMAGE IS SYMMETRIC.** `Δ_{k+1} = S − a·I`. -/
theorem rung_next_sym (r : Rung H K Δ) (B C : K) :
    (inner ℝ B (r.next C) : ℝ) = (inner ℝ (r.next B) C : ℝ) := by
  rw [Rung.next_apply, Rung.next_apply, inner_sub_right, inner_sub_left,
    real_inner_smul_right, real_inner_smul_left, rung_S_sym r B C]

/-- **THE LIFT IDENTITY — the engine of the whole tower.** The level-`(k+1)` quadratic form at `B`
is EXACTLY the level-`k` gauge-fixed form at the harmonic lift `u = G(Q*(S B))` of `B`. Every `a`
cancels: it enters through `M`, survives into `S`, and is subtracted again by `next`.

This is the identity implicit in `OnRangeCoercivity.next_coercive_gf_on_subspace`'s proof
(lines 299–322 there), isolated as an equality so that it can carry facts UPWARD (the curl
comparison of §7) rather than only inequalities downward. -/
theorem rung_inner_next_lift (r : Rung H K Δ) (B : K) :
    (inner ℝ B (r.next B) : ℝ)
      = (inner ℝ (r.G (r.Qstar (r.S B))) (Δ (r.G (r.Qstar (r.S B)))) : ℝ)
        + (inner ℝ (r.G (r.Qstar (r.S B))) (r.P (r.G (r.Qstar (r.S B)))) : ℝ) := by
  set u : H := r.G (r.Qstar (r.S B)) with hu
  have hQu : r.Q u = B := r.T_S B
  have hMu : r.M u = r.Qstar (r.S B) := r.M_G_right _
  have hval : (inner ℝ B (r.S B) : ℝ) = (inner ℝ u (r.M u) : ℝ) := by
    have h1 : (inner ℝ u (r.M u) : ℝ) = (inner ℝ (r.Qstar (r.S B)) u : ℝ) := by
      rw [hMu]
      exact real_inner_comm _ _
    rw [h1, r.hadj u (r.S B), hQu]
    exact real_inner_comm _ _
  have hinner := fineCLM_inner Δ r.P r.Q r.Qstar r.a r.hadj u
  have hM : r.M u = fineCLM Δ r.P r.Q r.Qstar r.a u := rfl
  rw [r.inner_next, hval, hM, hinner, hQu]
  ring

end RungFacts



/-! ## §7 — THE RG STEP PRESERVES THE INVARIANT

This is the theorem that makes a SECOND rung possible. `TowerOneStep` §10b named the missing object
as a strided bond-sector averaging operator; that was one of two obstructions. The other — the one
that actually blocks stacking — is that the level-`(k+1)` rung needs `hinj`/`hMpos` for the
**RG-image** operator `Δ_{k+1} = S_k − a·I`, and nothing in the tree said anything about that
operator's kernel. `Level.hcurl` is exactly the fact that closes it, and it survives the step:

`⟨B,Δ_{k+1}B⟩ = ⟨u,Δ_k u⟩ + ⟨u,P_k u⟩` (the lift identity, §6)
`≥ ⟨u,Δ_k u⟩ ≥ curlEnergy_k(u) ≥ 2·curlEnergy_{k+1}(Q_k u) = 2·curlEnergy_{k+1}(B)`,

the last step being `VRestrictedRoute`'s Stokes energy bound at `ell = 2`. So the invariant is
reproduced with a factor `2` to spare, and in particular it never degrades with the depth. -/

/-- **THE STEP.** From a level at `Λ` to a level at the halved lattice, with `op` the RG image. -/
noncomputable def stepLevel (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) {a : ℝ} (ha : 0 < a) :
    Level (coarseExtent Λ 2) where
  op := (levelRung lvl hdvd hwide ha).next
  hsym := fun u v => rung_next_sym (levelRung lvl hdvd hwide ha) u v
  hcurl := by
    intro B
    have hlift := rung_inner_next_lift (levelRung lvl hdvd hwide ha) B
    have hop : (inner ℝ ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))
        (piOp lvl.op 0 ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))) : ℝ)
        = (inner ℝ ((levelRung lvl hdvd hwide ha).G
            ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))
          (lvl.op ((levelRung lvl hdvd hwide ha).G
            ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))) : ℝ) := by
      simp [piOp]
    rw [hop] at hlift
    set u : BondFnL2 Λ := (levelRung lvl hdvd hwide ha).G
      ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)) with hu
    have hPnn : (0 : ℝ) ≤ (inner ℝ u ((levelRung lvl hdvd hwide ha).P u) : ℝ) :=
      pAxCLM_pos (CoarseLattice Λ 2) 2 u
    have hQu : (levelRung lvl hdvd hwide ha).Q u = B := (levelRung lvl hdvd hwide ha).T_S B
    have hofLp : WithLp.ofLp B
        = pullS (by norm_num) hdvd
          (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
      rw [← hQu]; rfl
    have hcurlB : curlEnergy (WithLp.ofLp B)
        = coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
      rw [hofLp]; exact curlEnergy_pullS _ _ _
    have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) (by norm_num) hdvd (WithLp.ofLp u)
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2] at hstokes
    have hlvlc := lvl.hcurl u
    have hnn := lvl.hpsd u
    rw [hcurlB]
    linarith

@[simp] theorem stepLevel_op (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) {a : ℝ} (ha : 0 < a) :
    (stepLevel lvl hdvd hwide ha).op = (levelRung lvl hdvd hwide ha).next := rfl



/-! ## §8 — THE `k`-UNIFORM COERCIVITY BOUND

`VRestrictedRoute` §6 proved `γ_V‖x‖² ≤ D + P` for every fine `x` whose coarse datum lies in the
source's subspace, at the FINE lattice, with `γ_V = 1/22522555753408512`. Its three inputs — the
master defect bound, the coarse fibre bound and Stokes — are theorems at EVERY periodic extent, and
`Level.hcurl` is exactly what is needed to read the first of them at a level whose operator is an
RG image rather than the lattice curl operator. So the SAME constant is obtained at every level.

Nothing here degrades with the depth: there is no `q^{2k}`, no tax, and no `gammaSeq`. -/

/-- **THE LEVEL-`Λ` GAUGE-FIXED BOUND ON THE PREIMAGE.** For every `u` whose level-`Λ` coarse datum
lies in the source's subspace at the next lattice, `γ_V‖u‖² ≤ ⟨u,Δ_Λu⟩ + ⟨u,P_Ax u⟩`, with the
`L`-free and level-free constant `γ_V = VRestrictedRoute.gammaV`. -/
theorem level_gf_on_preimage (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1)) (u : BondFnL2 Λ)
    (hu : VLat (coarseExtent Λ 2) (WithLp.ofLp (qLevel hdvd u))) :
    gammaV * ‖u‖ ^ 2 ≤ (inner ℝ u (lvl.op u) : ℝ)
      + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  have hfib := fibre_bound_on_VLat hdvd' hu
  rw [AdalyFormal.Balaban.FibreAggregate.gammaAgg_eq] at hfib
  have hofLp : WithLp.ofLp (qLevel hdvd u)
      = pullS (by norm_num) hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := rfl
  have hcurlA : curlEnergy (WithLp.ofLp (qLevel hdvd u))
      = coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [hofLp]; exact curlEnergy_pullS _ _ _
  have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) (by norm_num) hdvd (WithLp.ofLp u)
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hstokes
  have hlvlc := lvl.hcurl u
  have hZ : ‖qCLM (trivialU Λ) 2 u‖ ^ 2 = bondEnergy (WithLp.ofLp (qLevel hdvd u)) := by
    rw [← norm_qLevel hdvd u]
    exact norm_sq_eq_bondEnergy _
  have hdef := level_defect_bound lvl hdvd u
  rw [hZ] at hdef
  have hDnn : (0 : ℝ) ≤ (inner ℝ u (lvl.op u) : ℝ) := lvl.hpsd u
  have hPnn : (0 : ℝ) ≤ (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := pAxCLM_pos _ _ u
  rw [gammaV]
  rw [hcurlA] at hfib
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 22522555753408512)]
  linarith

/-- **THE ONE-STEP LAW AT A LEVEL.** The level-`(k+1)` operator — the RG image, on the halved
lattice's own bond carrier — is `γ_V/q²`-coercive on the source's subspace there. -/
theorem next_coercive_on_VLat (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1)
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1)) {a : ℝ} (ha : 0 < a)
    {B : BondFnL2 (coarseExtent Λ 2)} (hB : VLat (coarseExtent Λ 2) (WithLp.ofLp B)) :
    gammaV / ‖qCLM (trivialU Λ) 2‖ ^ 2 * ‖B‖ ^ 2
      ≤ (inner ℝ B ((levelRung lvl hdvd hwide ha).next B) : ℝ) := by
  refine AdalyFormal.Balaban.OnRangeCoercivity.next_coercive_gf_on_subspace
    (levelRung lvl hdvd hwide ha) gammaV_pos
    (fun C => VLat (coarseExtent Λ 2) (WithLp.ofLp C)) ?_ hB
  intro C hC
  have hQ : qLevel hdvd ((levelRung lvl hdvd hwide ha).G
      ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S C))) = C :=
    (levelRung lvl hdvd hwide ha).T_S C
  have hmain := level_gf_on_preimage lvl hdvd hdvd'
    ((levelRung lvl hdvd hwide ha).G
      ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S C)))
    (by rw [hQ]; exact hC)
  have hpi : (inner ℝ ((levelRung lvl hdvd hwide ha).G
        ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S C)))
      (piOp lvl.op 0 ((levelRung lvl hdvd hwide ha).G
        ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S C)))) : ℝ)
      = (inner ℝ ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S C)))
        (lvl.op ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S C)))) : ℝ) := by
    simp [piOp]
  rw [hpi]
  exact hmain

/-! ## §9 — THE TOWER, AND THE MILESTONE

The tower is a genuine recursion: level `0` is the lattice operator, and level `k+1` is the RG
image of level `k` — `op (k+1) = (rung k).next`, which is `TowerOneStep.Ladder`'s `law` on the
nose (`tower_law` below is `rfl`).

⚠ **WHY THIS IS NOT A `TowerOneStep.Ladder` TERM.** `Ladder` requires a rung at EVERY `k : ℕ`. On a
finite torus the extent tower terminates: `levelExtent L k μ + 1 = (L μ + 1)/2^k` (`levelExtent_spec`)
reaches `1` after finitely many halvings, and there the block no longer fits
(`LevelOK` fails). A total `Ladder` over the su(2) lattice therefore does not exist, and the
depth-bounded chain below is what a finite lattice supports. `TowerOneStep` §3 item 2 discloses
that `Ladder` is inhabited vacuously on trivial carriers; the depth bound here is the honest
alternative to inhabiting it that way. -/

/-- **THE TOWER.** `tower L ha k h` is the level-`k` operator with its invariant; `h` supplies the
admissibility of every level strictly below `k`. -/
noncomputable def tower (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) :
    ∀ (k : ℕ), (∀ i, i < k → LevelOK L i) → Level (levelExtent L k)
  | 0, _ => baseLevel L
  | (k + 1), h =>
      stepLevel (tower L ha k (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (h k (Nat.lt_succ_self k)).1 (h k (Nat.lt_succ_self k)).2 ha

@[simp] theorem tower_zero_op (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a)
    (h : ∀ i, i < 0 → LevelOK L i) :
    (tower L ha 0 h).op = deltaKCLMNormalized (trivialU L) := rfl

/-- **THE LADDER LAW, ON THE NOSE.** `op (k+1) = (rung k).next` — `TowerOneStep.Ladder.law`'s
equation, holding by `rfl` because the tower DEFINES the next operator as the RG image. -/
theorem tower_law (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) (k : ℕ)
    (h : ∀ i, i < k + 1 → LevelOK L i) :
    (tower L ha (k + 1) h).op
      = (levelRung (tower L ha k (fun i hi => h i (Nat.lt_succ_of_lt hi)))
          (h k (Nat.lt_succ_self k)).1 (h k (Nat.lt_succ_self k)).2 ha).next := rfl



/-! ## §10 — THE MILESTONE STATEMENT

`γ*` is a single global constant with no arguments: it is fixed BEFORE any lattice, any depth and
any field is named, which is the quantifier order the statement has to have to mean anything. -/

/-- **THE UNIFORM CONSTANT.** `γ* = γ_V = 1/22522555753408512`, `VRestrictedRoute`'s own constant,
reused rather than re-derived (LAW-19). -/
noncomputable def gammaStar : ℝ := gammaV

theorem gammaStar_pos : 0 < gammaStar := gammaV_pos

theorem gammaStar_eq : gammaStar = 1 / 22522555753408512 := rfl

/-- Admissibility of every level below `m`, from the extent condition. -/
theorem levelOK_below {k : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) {m : ℕ}
    (hm : m ≤ k + 1) : ∀ i, i < m → LevelOK L i :=
  fun _ hi => levelOK_of_pow hpow (by omega)

/-- The level-`j` operator of the depth-`(k+1)` tower. -/
noncomputable def towerAt (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k + 1) :
    Level (levelExtent L j) :=
  tower L ha j (levelOK_below hpow hj)

/-- Level `0` of the tower IS the lattice operator. -/
@[simp] theorem towerAt_zero (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (h0 : 0 ≤ k + 1) :
    (towerAt L ha hpow 0 h0).op = deltaKCLMNormalized (trivialU L) := rfl

/-- **THE TOWER LAW, ON THE TOWER'S OWN INDEXING.** -/
theorem towerAt_law (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    (towerAt L ha hpow (j + 1) (by omega)).op
      = (levelRung (towerAt L ha hpow j (by omega))
          (levelOK_of_pow hpow hj).1 (levelOK_of_pow hpow hj).2 ha).next :=
  rfl

/-- Every level at or below `k + 1` has an even side. -/
theorem levelExtent_even {k : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) {j : ℕ}
    (hj : j ≤ k + 1) : ∀ μ : Fin 3, (2 : ℕ) ∣ (levelExtent L j μ + 1) := by
  intro μ
  have h := levelExtent_dvd hpow (j := j) (by omega) μ
  exact dvd_trans (dvd_pow_self 2 (by omega : k + 2 - j ≠ 0)) h

/-- **THE MILESTONE — `k`-UNIFORM COERCIVITY ON THE SOURCE'S SUBSPACES.**

For every lattice `L`, every depth `k` admissible on `L` (`2^(k+2) ∣ L μ + 1`), and every level
`j ≤ k`: the level-`j` operator of the tower — the lattice operator at `j = 0`, the `j`-fold RG
image above it — is coercive with the constant `γ*` on the preimage of CMP99b p.428's subspace at
the level-`(j+1)` lattice.

`γ*` does not depend on `j`, on `k`, or on `L`. -/
theorem tower_uniform_coercive (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k)
    (u : BondFnL2 (levelExtent L j))
    (hu : VLat (levelExtent L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))) :
    gammaStar * ‖u‖ ^ 2
      ≤ (inner ℝ u ((towerAt L ha hpow j (by omega)).op u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) :=
  level_gf_on_preimage (towerAt L ha hpow j (by omega)) (levelOK_of_pow hpow hj).1
    (levelExtent_even hpow (j := j + 1) (by omega)) u hu

/-- **THE MILESTONE, COARSE SIDE.** The level-`(j+1)` operator — genuinely the RG image, on the
halved lattice's own carrier — is `γ*/q_j²`-coercive on the source's subspace there. -/
theorem tower_next_coercive (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k)
    {B : BondFnL2 (levelExtent L (j + 1))}
    (hB : VLat (levelExtent L (j + 1)) (WithLp.ofLp B)) :
    gammaStar / ‖qCLM (trivialU (levelExtent L j)) 2‖ ^ 2 * ‖B‖ ^ 2
      ≤ (inner ℝ B ((towerAt L ha hpow (j + 1) (by omega)).op B) : ℝ) :=
  next_coercive_on_VLat (towerAt L ha hpow j (by omega)) (levelOK_of_pow hpow hj).1
    (levelOK_of_pow hpow hj).2 (levelExtent_even hpow (j := j + 1) (by omega)) ha hB



/-! ## §11 — NON-VACUITY: the subspace at every level carries a nonzero vector

`TowerOneStep` §3 item 2 records the way a `k`-indexed tower statement goes empty: trivial carriers.
`TowerUniformSuTwo` went empty a second way, by `V := ⊥`. Both are blocked here by an EXPLICIT
nonzero element of `VLat` at every admissible level, transported from `VRestrictedRoute`'s own
witness (which is a named field with a computed value, not an existence statement). -/

/-- The reindexing is injective, so it does not collapse the witness. -/
theorem pullS_ne_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (Λ μ + 1))
    {F : CoarseBond Λ ell → SuTwo} (hF : F ≠ 0) :
    pullS hell hdvd F ≠ (0 : Bond (coarseExtent Λ ell) → SuTwo) := by
  intro h
  refine hF ?_
  funext c
  have h1 := congrFun h ((cbEquiv hell hdvd) c)
  have h2 : pullS hell hdvd F ((cbEquiv hell hdvd) c) = F c :=
    congrArg F ((cbEquiv hell hdvd).symm_apply_apply c)
  rw [h2] at h1
  exact h1

/-- **`VLat` IS NONDEGENERATE AT EVERY LATTICE WHOSE SIDE IS `4`-DIVISIBLE.** -/
theorem vLat_nontrivial (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (Λ μ + 1)) :
    ∃ A : Bond (coarseExtent Λ 2) → SuTwo, VLat (coarseExtent Λ 2) A ∧ A ≠ 0 := by
  obtain ⟨F, hF, hFne⟩ := AdalyFormal.Balaban.VRestrictedRoute.VSrc_nontrivial hdvd4
  exact ⟨pullS (by norm_num) (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) F,
    hF, pullS_ne_zero _ _ hFne⟩

/-- The same on the `ℓ²` carrier. -/
theorem vLat_carrier_nontrivial (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (Λ μ + 1)) :
    ∃ B : BondFnL2 (coarseExtent Λ 2), VLat (coarseExtent Λ 2) (WithLp.ofLp B) ∧ B ≠ 0 := by
  obtain ⟨A, hA, hAne⟩ := vLat_nontrivial (Λ := Λ) hdvd4
  refine ⟨WithLp.toLp 2 A, hA, ?_⟩
  intro h
  exact hAne (congrArg WithLp.ofLp h)

/-- **THE ZERO FIELD IS IN THE SUBSPACE.** All three clauses hold at `0`. Recorded because it is the
reason a fine-side witness must say more than `u ≠ 0`: the hypothesis `VLat Λ' (qLevel u)` is
satisfied by every `u` in `ker qLevel`, whatever `VLat` contains (see
`fine_hypothesis_kernel_route`, §12). -/
theorem vLat_zero (Λ' : PeriodicLatticeExtent) : VLat Λ' (0 : Bond Λ' → SuTwo) := by
  refine ⟨trivial, fun y _ b _ => rfl, fun c => ?_⟩
  have h : qCLM (trivialU Λ') 2 (0 : BondFnL2 Λ') = 0 := map_zero _
  exact congrFun (congrArg WithLp.ofLp h) c

/-- Every level at or below `k` has a `4`-divisible side, so §11's witness lives there. -/
theorem levelExtent_four {k : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) {j : ℕ}
    (hj : j ≤ k) : ∀ μ : Fin 3, (4 : ℕ) ∣ (levelExtent L j μ + 1) := by
  intro μ
  have h := levelExtent_dvd hpow (j := j) (by omega) μ
  have hle : (2 : ℕ) ^ 2 ∣ 2 ^ (k + 2 - j) := pow_dvd_pow 2 (by omega)
  exact dvd_trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2) (dvd_trans hle h)

/-- **THE MILESTONE IS NOT A STATEMENT ABOUT `{0}`.** At every level `j ≤ k` the subspace at the
next lattice carries a nonzero vector, and BOTH sides of the coarse-side milestone are strictly
positive there. -/
theorem milestone_nonvacuous (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    ∃ B : BondFnL2 (levelExtent L (j + 1)),
      VLat (levelExtent L (j + 1)) (WithLp.ofLp B) ∧ B ≠ 0
        ∧ 0 < gammaStar / ‖qCLM (trivialU (levelExtent L j)) 2‖ ^ 2 * ‖B‖ ^ 2
        ∧ 0 < (inner ℝ B ((towerAt L ha hpow (j + 1) (by omega)).op B) : ℝ) := by
  obtain ⟨B, hB, hBne⟩ := vLat_carrier_nontrivial (Λ := levelExtent L j) (levelExtent_four hpow hj)
  refine ⟨B, hB, hBne, ?_, ?_⟩
  · have hq : 0 < ‖qCLM (trivialU (levelExtent L j)) 2‖ :=
      AdalyFormal.Balaban.BridgeInverse.qCLM_norm_pos (by norm_num)
        (levelOK_of_pow hpow hj).1 (levelOK_of_pow hpow hj).2 _
    have hBn : 0 < ‖B‖ := norm_pos_iff.2 hBne
    have hg := gammaStar_pos
    positivity
  · have hmain := tower_next_coercive L ha hpow j hj hB
    have hq : 0 < ‖qCLM (trivialU (levelExtent L j)) 2‖ :=
      AdalyFormal.Balaban.BridgeInverse.qCLM_norm_pos (by norm_num)
        (levelOK_of_pow hpow hj).1 (levelOK_of_pow hpow hj).2 _
    have hBn : 0 < ‖B‖ := norm_pos_iff.2 hBne
    have hg := gammaStar_pos
    have hpos : 0 < gammaStar / ‖qCLM (trivialU (levelExtent L j)) 2‖ ^ 2 * ‖B‖ ^ 2 := by
      positivity
    exact lt_of_lt_of_le hpos hmain

/-- **THE FINE-SIDE MILESTONE IS NOT A STATEMENT ABOUT `{0}` EITHER.**

`milestone_nonvacuous` above witnesses the COARSE-side hypothesis form (`B ∈ VLat` directly). This
theorem witnesses `tower_uniform_coercive`'s OWN hypothesis — the DERIVED predicate
`VLat (levelExtent L (j+1)) (ofLp (qLevel … u))`, three definitions downstream of the free data —
at a NONZERO `u`, with both sides of that theorem's conclusion strictly positive. The two are
different hypotheses on different carriers, so one does not certify the other.

The witness is produced, not assumed: `vLat_carrier_nontrivial` supplies a nonzero `B` in the
subspace at the level-`(j+1)` lattice, `qLevel_surjective` (§5) pulls it back to some `u` with
`qLevel u = B`, and linearity forces `u ≠ 0` because `B ≠ 0`. The right-hand side's positivity is
obtained by APPLYING `tower_uniform_coercive` at this `u`, so the theorem exercises the headline
statement rather than re-deriving a look-alike.

⚠ **WHY THE `qLevel u ≠ 0` CONJUNCT IS THERE, AND WHY THE WITNESS WOULD BE WORTHLESS WITHOUT IT.**
`VLat Λ 0` is TRUE — all three clauses hold at the zero field — so the hypothesis
`VLat Λ_{j+1} (qLevel u)` is satisfied by EVERY `u` in the kernel of `qLevel`, whatever the subspace
contains. A witness drawn from that kernel would therefore certify nothing about `VLat`: it would
only show that `Q` has a kernel. The conjunct `qLevel u ≠ 0` excludes exactly that degenerate
route, and it holds here because the witness is a `qLevel`-preimage of a NONZERO element of the
subspace. -/
theorem tower_uniform_nonvacuous (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    ∃ u : BondFnL2 (levelExtent L j),
      VLat (levelExtent L (j + 1)) (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))
        ∧ u ≠ 0
        ∧ qLevel (levelOK_of_pow hpow hj).1 u ≠ 0
        ∧ 0 < gammaStar * ‖u‖ ^ 2
        ∧ 0 < (inner ℝ u ((towerAt L ha hpow j (by omega)).op u) : ℝ)
            + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) := by
  obtain ⟨B, hB, hBne⟩ := vLat_carrier_nontrivial (Λ := levelExtent L j) (levelExtent_four hpow hj)
  obtain ⟨u, hu⟩ := qLevel_surjective (Λ := levelExtent L j) (levelOK_of_pow hpow hj).1 B
  have hune : u ≠ 0 := by
    intro h
    refine hBne ?_
    rw [← hu, h]
    exact map_zero _
  have hVL : VLat (levelExtent L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u)) := by
    rw [hu]; exact hB
  have hQne : qLevel (levelOK_of_pow hpow hj).1 u ≠ 0 := by
    rw [hu]; exact hBne
  have hlhs : 0 < gammaStar * ‖u‖ ^ 2 := by
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hune
    have hg := gammaStar_pos
    positivity
  exact ⟨u, hVL, hune, hQne, hlhs,
    lt_of_lt_of_le hlhs (tower_uniform_coercive L ha hpow j hj u hVL)⟩

/-- **THE ENGINE'S DOMAIN IS NONEMPTY AT EVERY LATTICE, FOR EVERY LEVEL STRUCTURE.**
`tower_uniform_nonvacuous` witnesses the fine hypothesis along the tower's own levels. This
strengthens that to an ARBITRARY `Level Λ` at an arbitrary `4`-divisible lattice: the hypothesis
domain of `level_gf_on_preimage` — the engine every level of the tower reads — contains a `u` that
is nonzero AND whose coarse datum is a nonzero element of the subspace, whatever operator the level
carries. So the fine-side domain is not an artifact of the particular operators the tower builds. -/
theorem level_gf_on_preimage_nonvacuous (lvl : Level Λ)
    (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (Λ μ + 1)) :
    ∃ u : BondFnL2 Λ,
      VLat (coarseExtent Λ 2) (WithLp.ofLp
          (qLevel (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) u))
        ∧ u ≠ 0
        ∧ qLevel (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) u ≠ 0
        ∧ 0 < gammaV * ‖u‖ ^ 2
        ∧ 0 < (inner ℝ u (lvl.op u) : ℝ)
            + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  obtain ⟨B, hB, hBne⟩ := vLat_carrier_nontrivial (Λ := Λ) hdvd4
  obtain ⟨u, hu⟩ := qLevel_surjective
    (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) B
  have hune : u ≠ 0 := by
    intro h
    refine hBne ?_
    rw [← hu, h]
    exact map_zero _
  have hVL : VLat (coarseExtent Λ 2) (WithLp.ofLp
      (qLevel (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) u)) := by
    rw [hu]; exact hB
  have hQne : qLevel (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) u ≠ 0 := by
    rw [hu]; exact hBne
  have hlhs : 0 < gammaV * ‖u‖ ^ 2 := by
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hune
    have hg := gammaV_pos
    positivity
  exact ⟨u, hVL, hune, hQne, hlhs,
    lt_of_lt_of_le hlhs (level_gf_on_preimage lvl
      (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4)
      (AdalyFormal.Balaban.VRestrictedRoute.coarse_two_dvd hdvd4) u hVL)⟩

/-- **`VRestrictedRoute`'s OWN FINE-SIDE HYPOTHESIS, WITNESSED HERE.**

The same mismatch §3a records exists one module down: `VRestrictedRoute.coercive_on_VSrc_preimage`
is that module's fine-side theorem, with the DERIVED hypothesis
`VSrc hdvd4 (lineCoarseRestrictCov (trivialU L) 2 A)`, while the only existential nonvacuity theorem
in that module (`VSrc_nontrivial`) is the COARSE-side form `∃ B, VSrc hdvd4 B ∧ B ≠ 0`. `VSrc`
contains `0` as well, so the `ker Q` trap applies there verbatim.

This theorem supplies the missing witness in THAT module's own vocabulary — a nonzero `A` whose
coarse datum is a NONZERO element of `VSrc`, with both sides of that theorem's conclusion strictly
positive, the right-hand side obtained by APPLYING `coercive_on_VSrc_preimage` itself. It is stated
here rather than there because `VRestrictedRoute.lean` is outside this lane's write scope; moving it
is bookkeeping, the mathematics is done. -/
theorem vSrc_preimage_nonvacuous (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    ∃ A : Bond L → SuTwo,
      AdalyFormal.Balaban.VRestrictedRoute.VSrc hdvd4 (lineCoarseRestrictCov (trivialU L) 2 A)
        ∧ A ≠ 0
        ∧ lineCoarseRestrictCov (trivialU L) 2 A ≠ 0
        ∧ 0 < gammaV * bondEnergy A
        ∧ 0 < curlEnergy A + pAx A (CoarseLattice L 2) 2 := by
  obtain ⟨u, hVL, hune, hQne, hlhs, -⟩ := level_gf_on_preimage_nonvacuous (baseLevel L) hdvd4
  have hAne : (WithLp.ofLp u : Bond L → SuTwo) ≠ 0 := by
    intro h
    refine hune ?_
    refine (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).injective (funext (fun b => ?_))
    exact congrFun h b
  have hLne : lineCoarseRestrictCov (trivialU L) 2 (WithLp.ofLp u) ≠ 0 := by
    intro h
    refine hQne ?_
    have hq : qCLM (trivialU L) 2 u = 0 := by
      refine (WithLp.linearEquiv 2 ℝ (CoarseBond L 2 → SuTwo)).injective (funext (fun c => ?_))
      exact congrFun h c
    rw [qLevel_apply, hq, map_zero]
  have hbe : 0 < gammaV * bondEnergy (WithLp.ofLp u) := by
    rw [← norm_sq_eq_bondEnergy u]
    exact hlhs
  refine ⟨WithLp.ofLp u, hVL, hAne, hLne, hbe, ?_⟩
  exact lt_of_lt_of_le hbe
    (AdalyFormal.Balaban.VRestrictedRoute.coercive_on_VSrc_preimage hdvd4 (WithLp.ofLp u) hVL)




/-! ## §12 — CONTROLS

Two must-not-fire controls, on the two hypotheses the tower actually consumes. -/

section Controls

open AdalyFormal.Balaban.OnRangeCoercivity (siteConstCoarse)
open AdalyFormal.Balaban.FullySupplied (suTwoLift)
open AdalyFormal.Balaban.VRestrictedRoute (vWitFine vWitFine_vanishes_on_Ax vWitFine_Q_zero
  wSign VSrc_is_load_bearing)

/-- **MUST-NOT-FIRE 1 — the subspace hypothesis cannot be dropped.** `VRestrictedRoute`'s control,
read at `VLat`: the SAME site-constant coarse mode refutes the level-`0` conclusion for every
positive constant and is excluded by the subspace. `VLat` and `VSrc` are the same predicate
(`vLat_eq_vSrc`), so this transfers with no re-proof. -/
theorem vLat_is_load_bearing (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (Λ μ + 1))
    {g : Fin 3 → SuTwo} {ρ : Fin 3} (hg : g ρ ≠ 0) {γ : ℝ} (hγ : 0 < γ) :
    (¬ (γ * bondEnergy (suTwoLift 2 (siteConstCoarse (L := Λ) g))
        ≤ curlEnergy (suTwoLift 2 (siteConstCoarse (L := Λ) g))
          + pAx (suTwoLift 2 (siteConstCoarse (L := Λ) g)) (CoarseLattice Λ 2) 2))
      ∧ ¬ VLat (coarseExtent Λ 2)
          (pullS (by norm_num) (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4)
            (siteConstCoarse (L := Λ) g)) :=
  VSrc_is_load_bearing hdvd4 hg hγ

/-- A site whose `0`-coordinate is `1`; everything else `0`. -/
def oneSite (hpos : 1 < Λ 0 + 1) : PeriodicLatticeSite Λ :=
  Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite Λ) 0 ⟨1, hpos⟩

/-- `VRestrictedRoute`'s witness field takes the value `w` at a NAMED bond of `Λ`. -/
theorem vWitFine_value (hpos : 1 < Λ 0 + 1) (w : SuTwo) :
    vWitFine (Lc := Λ) w (oneSite hpos, (1 : Fin 3)) = w := by
  have hz0 : ((oneSite hpos) 0).val = 1 := by
    show (Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite Λ) 0
      (⟨1, hpos⟩ : Fin (Λ 0 + 1)) 0).val = 1
    rw [Function.update_self]
  have hz1 : ((oneSite hpos) 1).val = 0 := by
    show (Function.update (AdalyFormal.Balaban.FibreCoercivity.zeroSite Λ) 0
      (⟨1, hpos⟩ : Fin (Λ 0 + 1)) 1).val = 0
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    rfl
  show wSign ((oneSite hpos, (1 : Fin 3)) : Bond Λ) • w = w
  unfold wSign
  rw [if_pos ⟨rfl, by rw [hz0]⟩, if_pos (by rw [hz1]), one_smul]

theorem vWitFine_ne_zero (hpos : 1 < Λ 0 + 1) {w : SuTwo} (hw : w ≠ 0) :
    vWitFine (Lc := Λ) w ≠ (0 : Bond Λ → SuTwo) := by
  intro h
  refine hw ?_
  rw [← vWitFine_value hpos w, h]
  rfl

/-- **MUST-NOT-FIRE 2 — `Level.hcurl` is what makes the rung buildable, and it cannot be dropped.**

At the operator `Δ := 0` — symmetric and positive semidefinite, so it passes every OTHER hypothesis
a rung asks of its index operator — `M = Δ + P_Ax + a Q*Q` is NOT positive definite: the SAME
nonzero field annihilates all three terms. And that field is exactly where `Level.hcurl` fails,
because its curl energy is strictly positive. So the invariant is load-bearing, and
`level_fine_pos` is not a theorem that would hold anyway. -/
theorem hcurl_is_load_bearing (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1)) (hp : 1 < Λ 0 + 1)
    {w : SuTwo} (hw : w ≠ 0) (a : ℝ) :
    ∃ v : BondFnL2 Λ, v ≠ 0
      ∧ (0 : ℝ) < curlEnergy (WithLp.ofLp v)
      ∧ (inner ℝ v ((0 : BondFnL2 Λ →L[ℝ] BondFnL2 Λ) v) : ℝ) = 0
      ∧ (inner ℝ v (fineCLM (piOp (0 : BondFnL2 Λ →L[ℝ] BondFnL2 Λ) 0)
          (pAxCLM (CoarseLattice Λ 2) 2) (qLevel hdvd) (qLevelStar hdvd) a v) : ℝ) = 0 := by
  classical
  set A : Bond Λ → SuTwo := vWitFine (Lc := Λ) w with hA
  set v : BondFnL2 Λ := WithLp.toLp 2 A with hv
  have hAne : A ≠ 0 := vWitFine_ne_zero hp hw
  have hvne : v ≠ 0 := by
    intro h
    exact hAne (congrArg WithLp.ofLp h)
  -- the axial term vanishes
  have hpaxA : pAx A (CoarseLattice Λ 2) 2 = 0 :=
    pAx_eq_zero_of_vanishing_on_Ax A _ _ (fun y hy b hb => vWitFine_vanishes_on_Ax w hy hb)
  have hpax : (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ) = 0 := by
    rw [inner_pAxCLM_eq']
    exact hpaxA
  -- the averaging vanishes
  have hQA : ∀ c : CoarseBond Λ 2, lineCoarseRestrictCov (trivialU Λ) 2 A c = 0 :=
    fun c => vWitFine_Q_zero (hdvd 1) w c
  have hQ0 : qCLM (trivialU Λ) 2 v = 0 := by
    refine (WithLp.linearEquiv 2 ℝ (CoarseBond Λ 2 → SuTwo)).injective ?_
    funext c
    exact hQA c
  have hQnorm : ‖qLevel hdvd v‖ = 0 := by
    rw [norm_qLevel hdvd v, hQ0, norm_zero]
  -- the curl energy is strictly positive, from the fibre bound
  have hfib := AdalyFormal.Balaban.FibreAggregate.aggregate_fibre_bound_gamma hdvd A hQA
  rw [AdalyFormal.Balaban.FibreCoercivity.deltaK_trivialU_eq_curlEnergy, hpaxA, add_zero,
    AdalyFormal.Balaban.FibreAggregate.gammaAgg_eq] at hfib
  obtain ⟨b0, hb0⟩ : ∃ b0 : Bond Λ, A b0 ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hAne (funext hc)
  have hbe : (0 : ℝ) < bondEnergy A := AdalyFormal.Balaban.FibreAggregate.bondEnergy_pos A hb0
  refine ⟨v, hvne, ?_, ?_, ?_⟩
  · have : WithLp.ofLp v = A := rfl
    rw [this]
    linarith
  · simp
  · rw [fineCLM_inner _ _ _ _ _ (qLevel_hadj hdvd) v, hpax, hQnorm]
    have hz : (inner ℝ v (piOp (0 : BondFnL2 Λ →L[ℝ] BondFnL2 Λ) 0 v) : ℝ) = 0 := by
      simp [piOp]
    rw [hz]
    ring

/-- **MUST-NOT-FIRE 3 — `u ≠ 0` ALONE CERTIFIES NOTHING ON THE FINE SIDE.**

`tower_uniform_coercive`'s hypothesis is `VLat Λ_{j+1} (qLevel u)`, and `VLat Λ' 0` is true
(`vLat_zero`). So EVERY nonzero element of `ker qLevel` satisfies that hypothesis for a reason
having nothing whatever to do with the subspace's content. This theorem exhibits such an element —
`VRestrictedRoute`'s own `vWitFine`, the same field that powers `hcurl_is_load_bearing`, whose
averaging vanishes identically (`vWitFine_Q_zero`).

Consequence, and the reason §11's fine-side witnesses carry the extra conjunct `qLevel u ≠ 0`: a
witness certifying only `u ≠ 0` would be satisfied by this field and would therefore prove nothing
about `VLat`. The strengthened witnesses exclude it in the kernel, not in prose. -/
theorem fine_hypothesis_kernel_route (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hp : 1 < Λ 0 + 1) {w : SuTwo} (hw : w ≠ 0) :
    ∃ v : BondFnL2 Λ, v ≠ 0
      ∧ qLevel hdvd v = 0
      ∧ VLat (coarseExtent Λ 2) (WithLp.ofLp (qLevel hdvd v)) := by
  classical
  set A : Bond Λ → SuTwo := vWitFine (Lc := Λ) w with hA
  set v : BondFnL2 Λ := WithLp.toLp 2 A with hv
  have hAne : A ≠ 0 := vWitFine_ne_zero hp hw
  have hvne : v ≠ 0 := by
    intro h
    exact hAne (congrArg WithLp.ofLp h)
  have hQ0 : qCLM (trivialU Λ) 2 v = 0 := by
    refine (WithLp.linearEquiv 2 ℝ (CoarseBond Λ 2 → SuTwo)).injective ?_
    funext c
    exact vWitFine_Q_zero (hdvd 1) w c
  have hqL : qLevel hdvd v = 0 := by
    rw [qLevel_apply, hQ0, map_zero]
  refine ⟨v, hvne, hqL, ?_⟩
  rw [hqL]
  exact vLat_zero (coarseExtent Λ 2)

end Controls



/-! ## §13 — A CONCRETE INSTANCE AT DEPTH `2`

`L μ = 15` (side `16`) satisfies `2^(1+2) ∣ 16`, so `k = 1`: levels `0` and `1` are admissible and
the tower runs to level `2`. The extents are `15 → 7 → 3`, computed by the kernel, not asserted. -/

section Depth2

/-- Side `16` in every direction. -/
def witL : PeriodicLatticeExtent := fun _ => 15

theorem witL_pow : ∀ μ : Fin 3, (2 : ℕ) ^ (1 + 2) ∣ (witL μ + 1) := by decide

/-- The extent tower on `witL`, computed. -/
theorem witL_extents : (∀ μ : Fin 3, levelExtent witL 0 μ = 15)
    ∧ (∀ μ : Fin 3, levelExtent witL 1 μ = 7)
    ∧ (∀ μ : Fin 3, levelExtent witL 2 μ = 3) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;>
    · show (_ : ℕ) = _
      simp only [levelExtent, coarseExtent, witL]

/-- `4` is NOT admissible: the depth stops, and it stops for the stated reason. -/
theorem witL_level_three_not_ok : ¬ LevelOK witL 3 := by
  intro h
  have := h.2 0
  have hval : levelExtent witL 3 0 = 1 := by decide
  omega

theorem one_pos_real : (0 : ℝ) < 1 := by norm_num

/-- **THE DEPTH-`2` STATEMENT, WITH A NONZERO WITNESS AND BOTH SIDES POSITIVE.** The operator is
`(tower witL 2).op`, i.e. the RG image of the RG image of the lattice operator — two genuine steps,
on a carrier whose lattice has shrunk `16 → 8 → 4` per side. -/
theorem depth_two_nonvacuous :
    ∃ B : BondFnL2 (levelExtent witL 2),
      VLat (levelExtent witL 2) (WithLp.ofLp B) ∧ B ≠ 0
        ∧ 0 < gammaStar / ‖qCLM (trivialU (levelExtent witL 1)) 2‖ ^ 2 * ‖B‖ ^ 2
        ∧ 0 < (inner ℝ B ((towerAt witL one_pos_real witL_pow 2 (by omega)).op B) : ℝ) :=
  milestone_nonvacuous witL one_pos_real witL_pow 1 (le_refl 1)

/-- The depth-`1` statement on the same lattice, so that the `j`-quantifier is exercised at two
different values on ONE lattice. -/
theorem depth_one_nonvacuous :
    ∃ B : BondFnL2 (levelExtent witL 1),
      VLat (levelExtent witL 1) (WithLp.ofLp B) ∧ B ≠ 0
        ∧ 0 < gammaStar / ‖qCLM (trivialU (levelExtent witL 0)) 2‖ ^ 2 * ‖B‖ ^ 2
        ∧ 0 < (inner ℝ B ((towerAt witL one_pos_real witL_pow 1 (by omega)).op B) : ℝ) :=
  milestone_nonvacuous witL one_pos_real witL_pow 0 (by omega)

/-- **THE FINE-SIDE HEADLINE, AT `j = 0` ON A CLOSED NUMERAL LATTICE.** `tower_uniform_coercive`'s
own hypothesis is satisfied by a nonzero `u` on the level-`0` carrier of `witL` (side `16`), with
both sides of its conclusion strictly positive. -/
theorem tower_uniform_depth_zero_nonvacuous :
    ∃ u : BondFnL2 (levelExtent witL 0),
      VLat (levelExtent witL 1)
          (WithLp.ofLp (qLevel (levelOK_of_pow witL_pow (show (0 : ℕ) ≤ 1 by omega)).1 u))
        ∧ u ≠ 0
        ∧ qLevel (levelOK_of_pow witL_pow (show (0 : ℕ) ≤ 1 by omega)).1 u ≠ 0
        ∧ 0 < gammaStar * ‖u‖ ^ 2
        ∧ 0 < (inner ℝ u ((towerAt witL one_pos_real witL_pow 0 (by omega)).op u) : ℝ)
            + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent witL 0) 2) 2 u) : ℝ) :=
  tower_uniform_nonvacuous witL one_pos_real witL_pow 0 (by omega)

/-- **THE FINE-SIDE HEADLINE, AT `j = 1` ON THE SAME LATTICE.** The carrier is now the once-halved
lattice and the operator is a genuine RG image, so the `j`-quantifier of `tower_uniform_coercive` is
exercised at two different values against one `L`. -/
theorem tower_uniform_depth_one_nonvacuous :
    ∃ u : BondFnL2 (levelExtent witL 1),
      VLat (levelExtent witL 2)
          (WithLp.ofLp (qLevel (levelOK_of_pow witL_pow (show (1 : ℕ) ≤ 1 by omega)).1 u))
        ∧ u ≠ 0
        ∧ qLevel (levelOK_of_pow witL_pow (show (1 : ℕ) ≤ 1 by omega)).1 u ≠ 0
        ∧ 0 < gammaStar * ‖u‖ ^ 2
        ∧ 0 < (inner ℝ u ((towerAt witL one_pos_real witL_pow 1 (by omega)).op u) : ℝ)
            + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent witL 1) 2) 2 u) : ℝ) :=
  tower_uniform_nonvacuous witL one_pos_real witL_pow 1 (le_refl 1)

/-- **THE TWO LEVELS ARE THE SAME CONSTANT.** `γ*` at depth `1` and at depth `2` is one number. -/
theorem depth_constant_is_uniform :
    gammaStar = 1 / 22522555753408512 ∧ (0 : ℝ) < gammaStar :=
  ⟨gammaStar_eq, gammaStar_pos⟩

end Depth2



/-! ## §14 — THE `q` IS `L`-FREE AND LEVEL-FREE, SO THE COARSE-SIDE CONSTANT IS TOO

`tower_next_coercive`'s constant is `γ*/q_j²` with `q_j = ‖Q_j‖`, which is a priori a different
number at every level. It is not: `‖qCLM (trivialU Λ) 2‖ ≤ √(1/8)` at EVERY lattice.

`VRestrictedRoute`'s header records that `qCLM U ell` and `StridedAveraging.qStepCLM 1 U ell` are
"two candidate readings … not proved equal here (that intertwining is not built in this tree)".
It is built here, from `StridedAveraging.stepBondAvg_one`, and then `qStepCLM_opNorm_le` supplies
the bound. -/

section QNorm

open AdalyFormal.Balaban.StridedAveraging (coarseBondOneEquiv stepBondAvg stepBondAvg_one qStepCLM
  qStepCLM_opNorm_le)

/-- The stride-`1` coarse carrier IS the fine bond carrier, as a linear isometry. -/
noncomputable def oneIso (Λ : PeriodicLatticeExtent) : BondFnL2 Λ ≃ₗᵢ[ℝ] CoarseFnL2 Λ 1 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (coarseBondOneEquiv Λ).symm

/-- **THE INTERTWINING, POINTWISE.** `stepBondAvg` at stride `1` IS `lineCoarseRestrictCov`. -/
theorem qStep_apply_eq (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) (x : BondFnL2 Λ)
    (b : CoarseBond Λ 2) :
    stepBondAvg 1 (trivialU Λ) 2 (WithLp.ofLp (oneIso Λ x)) b
      = lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp x) b :=
  stepBondAvg_one (L := Λ) (trivialU Λ) (ell := 2) (WithLp.ofLp x) b b rfl rfl
    (by have := hwide b.2; omega)

/-- **THE INTERTWINING.** `qCLM U 2 = qStepCLM 1 U 2` through the stride-`1` identification. -/
theorem qCLM_eq_qStep (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) (x : BondFnL2 Λ) :
    (qStepCLM 1 (trivialU Λ) 2 (oneIso Λ x) : CoarseFnL2 Λ 2) = qCLM (trivialU Λ) 2 x := by
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond Λ 2 → SuTwo)).injective (funext (fun b => ?_))
  exact qStep_apply_eq hwide x b

/-- **THE `L`-FREE OPERATOR-NORM BOUND.** `‖Q‖ ≤ √(1/8)` at every compatible lattice. -/
theorem qCLM_opNorm_le (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) :
    ‖qCLM (trivialU Λ) 2‖ ≤ Real.sqrt (1 / 8) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun x => ?_)
  have h3 : ‖qStepCLM 1 (trivialU Λ) 2‖ ≤ Real.sqrt (1 / ((2 : ℕ) : ℝ) ^ 3) :=
    qStepCLM_opNorm_le (by norm_num) (by norm_num)
      (fun ν => by simpa using hdvd ν) (trivialU Λ)
  have h5 : Real.sqrt (1 / ((2 : ℕ) : ℝ) ^ 3) = Real.sqrt (1 / 8) := by norm_num
  rw [h5] at h3
  have h2 : ‖qStepCLM 1 (trivialU Λ) 2 (oneIso Λ x)‖
      ≤ ‖qStepCLM 1 (trivialU Λ) 2‖ * ‖oneIso Λ x‖ :=
    (qStepCLM 1 (trivialU Λ) 2).le_opNorm _
  have h4 : ‖oneIso Λ x‖ = ‖x‖ := (oneIso Λ).norm_map x
  have h1 : ‖qCLM (trivialU Λ) 2 x‖ = ‖qStepCLM 1 (trivialU Λ) 2 (oneIso Λ x)‖ := by
    rw [qCLM_eq_qStep hwide x]
  rw [h4] at h2
  have h6 : ‖qStepCLM 1 (trivialU Λ) 2‖ * ‖x‖ ≤ Real.sqrt (1 / 8) * ‖x‖ :=
    mul_le_mul_of_nonneg_right h3 (norm_nonneg x)
  rw [h1]
  linarith

theorem qCLM_normSq_le (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) :
    ‖qCLM (trivialU Λ) 2‖ ^ 2 ≤ 1 / 8 := by
  have h := qCLM_opNorm_le hdvd hwide
  have hs : Real.sqrt (1 / 8) ^ 2 = 1 / 8 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (qCLM (trivialU Λ) 2), Real.sqrt_nonneg (1 / 8 : ℝ)]

/-- **THE MILESTONE, WITH A FULLY EXPLICIT LEVEL-FREE AND `L`-FREE CONSTANT.** `8γ*` on the
source's subspace at every admissible level. -/
theorem tower_next_coercive_uniform (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k)
    {B : BondFnL2 (levelExtent L (j + 1))}
    (hB : VLat (levelExtent L (j + 1)) (WithLp.ofLp B)) :
    8 * gammaStar * ‖B‖ ^ 2
      ≤ (inner ℝ B ((towerAt L ha hpow (j + 1) (by omega)).op B) : ℝ) := by
  have hmain := tower_next_coercive L ha hpow j hj hB
  have hq2 := qCLM_normSq_le (Λ := levelExtent L j) (levelOK_of_pow hpow hj).1
    (levelOK_of_pow hpow hj).2
  have hqpos : 0 < ‖qCLM (trivialU (levelExtent L j)) 2‖ :=
    AdalyFormal.Balaban.BridgeInverse.qCLM_norm_pos (by norm_num)
      (levelOK_of_pow hpow hj).1 (levelOK_of_pow hpow hj).2 _
  have hq2pos : (0 : ℝ) < ‖qCLM (trivialU (levelExtent L j)) 2‖ ^ 2 := by positivity
  have hstep : 8 * gammaStar ≤ gammaStar / ‖qCLM (trivialU (levelExtent L j)) 2‖ ^ 2 := by
    rw [le_div_iff₀ hq2pos]
    nlinarith [gammaStar_pos]
  have hBsq : (0 : ℝ) ≤ ‖B‖ ^ 2 := sq_nonneg _
  exact le_trans (mul_le_mul_of_nonneg_right hstep hBsq) hmain

/-- **THE `8γ*` FORM IS NOT A STATEMENT ABOUT `{0}`.** `tower_next_coercive_uniform` has the same
hypothesis as `tower_next_coercive` but a different conclusion (the `q`-free constant `8γ*`), so it
gets its own witness rather than borrowing `milestone_nonvacuous`: the right-hand side's positivity
is obtained by APPLYING `tower_next_coercive_uniform` at the exhibited nonzero `B`. -/
theorem tower_next_uniform_nonvacuous (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    ∃ B : BondFnL2 (levelExtent L (j + 1)),
      VLat (levelExtent L (j + 1)) (WithLp.ofLp B) ∧ B ≠ 0
        ∧ 0 < 8 * gammaStar * ‖B‖ ^ 2
        ∧ 0 < (inner ℝ B ((towerAt L ha hpow (j + 1) (by omega)).op B) : ℝ) := by
  obtain ⟨B, hB, hBne⟩ := vLat_carrier_nontrivial (Λ := levelExtent L j) (levelExtent_four hpow hj)
  have hlhs : 0 < 8 * gammaStar * ‖B‖ ^ 2 := by
    have hBn : 0 < ‖B‖ := norm_pos_iff.2 hBne
    have hg := gammaStar_pos
    positivity
  exact ⟨B, hB, hBne, hlhs,
    lt_of_lt_of_le hlhs (tower_next_coercive_uniform L ha hpow j hj hB)⟩

/-- The same at the closed numeral lattice `witL`, at the deepest admissible level (`j = 1`, i.e.
the operator after TWO RG steps). -/
theorem tower_next_uniform_depth_two_nonvacuous :
    ∃ B : BondFnL2 (levelExtent witL 2),
      VLat (levelExtent witL 2) (WithLp.ofLp B) ∧ B ≠ 0
        ∧ 0 < 8 * gammaStar * ‖B‖ ^ 2
        ∧ 0 < (inner ℝ B ((towerAt witL one_pos_real witL_pow 2 (by omega)).op B) : ℝ) :=
  tower_next_uniform_nonvacuous witL one_pos_real witL_pow 1 (le_refl 1)

end QNorm



/-! ## §16 — THE TOWER IS NOT THE LATTICE: the `j`-index is not decorative

`stepLevel`'s invariant is proved with a factor `2` to spare (§7). Exposing the sharp form turns
that slack into a SEPARATION: the level-`(j+1)` operator is not the lattice operator at the
level-`(j+1)` lattice. This is the positive, proved form of the fact that forced §2 item 4's
architecture — there is no ladder of honest lattice rungs, because the RG image and the lattice
operator at the next scale are DIFFERENT OPERATORS. -/

section Separation

/-- **THE SHARP STEP BOUND.** `2·curlEnergy_{k+1}(B) ≤ ⟨B, Δ_{k+1} B⟩` — the factor `stepLevel`
discards in order to keep the invariant uniform. -/
theorem step_curl_sharp (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) {a : ℝ} (ha : 0 < a)
    (B : BondFnL2 (coarseExtent Λ 2)) :
    2 * curlEnergy (WithLp.ofLp B)
      ≤ (inner ℝ B ((levelRung lvl hdvd hwide ha).next B) : ℝ) := by
  have hlift := rung_inner_next_lift (levelRung lvl hdvd hwide ha) B
  have hop : (inner ℝ ((levelRung lvl hdvd hwide ha).G
        ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))
      (piOp lvl.op 0 ((levelRung lvl hdvd hwide ha).G
        ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))) : ℝ)
      = (inner ℝ ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))
        (lvl.op ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))) : ℝ) := by
    simp [piOp]
  rw [hop] at hlift
  set u : BondFnL2 Λ := (levelRung lvl hdvd hwide ha).G
    ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)) with hu
  have hPnn : (0 : ℝ) ≤ (inner ℝ u ((levelRung lvl hdvd hwide ha).P u) : ℝ) :=
    pAxCLM_pos (CoarseLattice Λ 2) 2 u
  have hQu : (levelRung lvl hdvd hwide ha).Q u = B := (levelRung lvl hdvd hwide ha).T_S B
  have hofLp : WithLp.ofLp B
      = pullS (by norm_num) hdvd
        (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [← hQu]; rfl
  have hcurlB : curlEnergy (WithLp.ofLp B)
      = coarseCurlEnergy hdvd (lineCoarseRestrictCov (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [hofLp]; exact curlEnergy_pullS _ _ _
  have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) (by norm_num) hdvd (WithLp.ofLp u)
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hstokes
  have hlvlc := lvl.hcurl u
  rw [hcurlB]
  linarith

/-- **THE SEPARATION.** At every admissible level the tower's operator DIFFERS from the lattice
operator at that lattice. The witness is the subspace's own nonzero element: its curl energy is
strictly positive (fibre bound), the tower's form is at least twice it (`step_curl_sharp`), and the
lattice form IS it (`inner_deltaK_flat`). -/
theorem towerAt_op_ne_lattice (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    (towerAt L ha hpow (j + 1) (by omega)).op
      ≠ deltaKCLMNormalized (trivialU (levelExtent L (j + 1))) := by
  intro hcon
  obtain ⟨B, hB, hBne⟩ := vLat_carrier_nontrivial (Λ := levelExtent L j) (levelExtent_four hpow hj)
  -- the witness has strictly positive curl energy
  have hfib := fibre_bound_on_VLat (Λ := levelExtent L (j + 1))
    (levelExtent_even hpow (j := j + 1) (by omega)) hB
  rw [AdalyFormal.Balaban.FibreAggregate.gammaAgg_eq] at hfib
  have hbe : (0 : ℝ) < bondEnergy (WithLp.ofLp B) := by
    have hn : ‖B‖ ^ 2 = bondEnergy (WithLp.ofLp B) := norm_sq_eq_bondEnergy B
    have : (0 : ℝ) < ‖B‖ ^ 2 := pow_pos (norm_pos_iff.2 hBne) 2
    linarith
  have hscale : (0 : ℝ) < 1 / 3316224 * bondEnergy (WithLp.ofLp B) :=
    mul_pos (by norm_num) hbe
  have hcurlpos : (0 : ℝ) < curlEnergy (WithLp.ofLp B) := lt_of_lt_of_le hscale hfib
  -- the tower's form is at least twice the curl energy
  have hsharp := step_curl_sharp (towerAt L ha hpow j (by omega))
    (levelOK_of_pow hpow hj).1 (levelOK_of_pow hpow hj).2 ha B
  -- the lattice's form IS the curl energy
  have hlat : (inner ℝ B (deltaKCLMNormalized (trivialU (levelExtent L (j + 1))) B) : ℝ)
      = curlEnergy (WithLp.ofLp B) := inner_deltaK_flat B
  have hEq : (inner ℝ B ((towerAt L ha hpow (j + 1) (by omega)).op B) : ℝ)
      = (inner ℝ B (deltaKCLMNormalized (trivialU (levelExtent L (j + 1))) B) : ℝ) := by
    rw [hcon]
  rw [hlat] at hEq
  have hEq2 : (inner ℝ B ((levelRung (towerAt L ha hpow j (by omega))
      (levelOK_of_pow hpow hj).1 (levelOK_of_pow hpow hj).2 ha).next B) : ℝ)
      = curlEnergy (WithLp.ofLp B) := hEq
  linarith

/-- **THE LEVEL-`0` CASE AGREES WITH `VRestrictedRoute`, BY TWO ROUTES.** The left conjunct is this
module's general machinery instantiated at `baseLevel`; the right is `VRestrictedRoute`'s own
level-`0` theorem. Stated as a conjunction so the kernel checks they are the same statement, not a
look-alike — a second, independent path on the one level both cover. -/
theorem level_zero_two_routes_agree (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) (u : BondFnL2 L)
    (hu : VLat (coarseExtent L 2)
      (WithLp.ofLp (qLevel (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4) u))) :
    (gammaStar * ‖u‖ ^ 2
        ≤ curlEnergy (WithLp.ofLp u) + pAx (WithLp.ofLp u) (CoarseLattice L 2) 2)
      ∧ (gammaStar * ‖u‖ ^ 2
        ≤ curlEnergy (WithLp.ofLp u) + pAx (WithLp.ofLp u) (CoarseLattice L 2) 2) := by
  constructor
  · have h := level_gf_on_preimage (baseLevel L)
      (AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4)
      (AdalyFormal.Balaban.VRestrictedRoute.coarse_two_dvd hdvd4) u hu
    rw [baseLevel_op, inner_deltaK_flat, inner_pAxCLM_eq'] at h
    exact h
  · have h := AdalyFormal.Balaban.VRestrictedRoute.coercive_on_VSrc_preimage hdvd4
      (WithLp.ofLp u) hu
    have hn : ‖u‖ ^ 2 = bondEnergy (WithLp.ofLp u) := norm_sq_eq_bondEnergy u
    rw [hn]
    exact h

end Separation

/-! ## §15 — AXIOM AUDIT: every declaration in this module.

Generated mechanically from the file's own declaration headers by
`compute/tower_milestone/gen_axiom_list.py` (the script `TowerOneStep` uses, retargeted — LAW-19),
so the list cannot silently fall behind the code: 85 declarations, 85 prints (75 at the prosecuted
commit `5dfe7f6d`, plus the nine declarations §3a adds: seven nonvacuity witnesses, the
surjectivity input `qLevel_surjective`, and `vLat_zero`). -/

#print axioms levelExtent
#print axioms levelExtent_zero
#print axioms levelExtent_succ
#print axioms levelExtent_spec
#print axioms levelExtent_dvd
#print axioms LevelOK
#print axioms levelOK_of_pow
#print axioms VLat
#print axioms vLat_eq_vSrc
#print axioms fibre_bound_on_VLat
#print axioms Level
#print axioms Level.hpsd
#print axioms baseLevel
#print axioms baseLevel_op
#print axioms level_defect_bound
#print axioms level_fine_pos
#print axioms coarseIso
#print axioms coarseIso_ofLp
#print axioms qLevel
#print axioms qLevelStar
#print axioms qLevel_apply
#print axioms qLevelStar_apply
#print axioms norm_qLevel
#print axioms qLevel_hadj
#print axioms qLevelStar_injective
#print axioms qLevel_surjective
#print axioms levelRung
#print axioms rung_G_sym
#print axioms rung_T_sym
#print axioms rung_S_sym
#print axioms rung_next_sym
#print axioms rung_inner_next_lift
#print axioms stepLevel
#print axioms stepLevel_op
#print axioms level_gf_on_preimage
#print axioms next_coercive_on_VLat
#print axioms tower
#print axioms tower_zero_op
#print axioms tower_law
#print axioms gammaStar
#print axioms gammaStar_pos
#print axioms gammaStar_eq
#print axioms levelOK_below
#print axioms towerAt
#print axioms towerAt_zero
#print axioms towerAt_law
#print axioms levelExtent_even
#print axioms tower_uniform_coercive
#print axioms tower_next_coercive
#print axioms pullS_ne_zero
#print axioms vLat_nontrivial
#print axioms vLat_carrier_nontrivial
#print axioms vLat_zero
#print axioms levelExtent_four
#print axioms milestone_nonvacuous
#print axioms tower_uniform_nonvacuous
#print axioms level_gf_on_preimage_nonvacuous
#print axioms vSrc_preimage_nonvacuous
#print axioms vLat_is_load_bearing
#print axioms oneSite
#print axioms vWitFine_value
#print axioms vWitFine_ne_zero
#print axioms hcurl_is_load_bearing
#print axioms fine_hypothesis_kernel_route
#print axioms witL
#print axioms witL_pow
#print axioms witL_extents
#print axioms witL_level_three_not_ok
#print axioms one_pos_real
#print axioms depth_two_nonvacuous
#print axioms depth_one_nonvacuous
#print axioms tower_uniform_depth_zero_nonvacuous
#print axioms tower_uniform_depth_one_nonvacuous
#print axioms depth_constant_is_uniform
#print axioms oneIso
#print axioms qStep_apply_eq
#print axioms qCLM_eq_qStep
#print axioms qCLM_opNorm_le
#print axioms qCLM_normSq_le
#print axioms tower_next_coercive_uniform
#print axioms tower_next_uniform_nonvacuous
#print axioms tower_next_uniform_depth_two_nonvacuous
#print axioms step_curl_sharp
#print axioms towerAt_op_ne_lattice
#print axioms level_zero_two_routes_agree

end AdalyFormal.Balaban.TowerMilestone
