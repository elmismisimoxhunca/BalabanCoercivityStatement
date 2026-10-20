/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaPrime
import AdalyFormal.Balaban.CovariantHjMinimizer

set_option autoImplicit false

/-!
# `J` and `D̃⁽²⁾` — two of CMP99b (3.156)'s opaque ingredients

**Dispatch target**: `DeltaKRecursive.lean`'s `RGScaleFamily.J`/`RGScaleFamily.Dtilde2` fields are
carried OPAQUE there (page-cited, never assumed). This file builds both, page-cited and
image-verified, and reports precisely what remains external.

## SOURCES, VERBATIM, IMAGE-VERIFIED (300 dpi, `compute/j_renders/`, printed headers checked)

**CMP99b p.392** (`compute/j_renders/CMP99b_p392-04.png`, header "392 / T. Balaban" confirmed),
eq. (3.8)-(3.9)-(3.11)-(3.13):

```
(D*A)(x) = Σ_{μ=1}^d η⁻¹(R(U(x,x-ηe_μ))A(x-ηe_μ,x) - A(x,x+ηe_μ))
         = Σ_μ (D*_μ A_μ)(x) = Σ_μ (DA_μ)(x,x-ηe_μ).                                    (3.8)

(D*F)(x,x+ηe_μ) = (D*F)_μ(x) = Σ_{ν<μ}(D*_ν F_{νμ})(x) - Σ_{ν>μ}(D*_ν F_{μν})(x)
                = Σ_{ν=1}^d (D*_ν F_{νμ})(x),                                            (3.9)

where F_{μν}(x) = F(p_{μν}(x)), and in the last equality above we have assumed that
F_{μν}(x) = -F_{νμ}(x).
                                     ⋮
⟨A,J⟩ = Σ_{b⊂T_η} η^d tr A(b)J(b),                                                       (3.11)

where J = D*η⁻²Im∂U, (∂U)(p) = U(∂p).
                                     ⋮
Q_j(U,ηA) = (1/i) log (‾‾‾‾‾‾‾‾(exp iηA))^j.                                              (3.13)
```

**CMP99b p.421** (`compute/j_renders/CMP99b_p421-33.png`, header "Propagators for Lattice Gauge
Theories / 421" confirmed), the text immediately after eq. (3.127):

> "The function `C^{(2)}(A)` is defined at bonds of `𝔅`, and on `Λ_j` it coincides with
> `C_j^{(2)}(L^jηA)` — a second order term in the expansion of `Q_j(ηA)`."

**CMP99b p.427** (`corpus/pages/CMP99b_p427.md`, `verification_status: adjudicated`), eq. (3.155)'s
own prose:

> "the function `D̃⁽²⁾(B)` is a quadratic polynomial in `B` with properties similar to `C^{(2)}(A)`,
> only restricted to unit blocks"

**CMP99b p.428** (`corpus/pages/CMP99b_p428.md`, `verification_status: adjudicated`), eq. (3.156):

```
⟨B,(QG₁Q*)⁻¹B⟩ - a⟨B,B⟩ - 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩.
```

**CMP109 p.261** (`compute/j_renders/CMP109_p261-13.png`, header "Renormalization Group Approach to
Lattice Field Theories / 261" confirmed), eq. (1.5)/(1.8):

```
⟨B,Δ^{(j)}(U_k)B⟩ = ⟨H_{1,j}(U_k)B,Δ_1(U_k)H_{1,j}(U_k)B⟩
                     - 2⟨H_{1,j}(U_k)hC̃^{(2)}(Ū_k^j,B),J⟩ + G^{(2)}(B),                  (1.5)

where the operators H_{1,j}, Δ_1 are defined in Sect. D [13], and C̃^{(2)}(Ū_k^j,B) is the
second order polynomial in the expansion of Q̃(Ū_k^j,B).
                                     ⋮
J_j = D_{Ũ_j}^{ξ*} ξ⁻² π Im ∂U_j,                                                        (1.8)

where π denotes the projection in the space of all complex N×N-matrices onto the algebra `𝔤ᶜ`,
and Im U = (1/2i)(U-U⁻¹).
```

## VERDICT 1 — CMP99b's `J` (eqs. 3.11, 3.155, 3.156) IS CMP109's `J_j` (eq. 1.8)

Both formulas are **`D* applied to (spacing)⁻² · π · Im ∂U`** — CMP99b: `J = D*η⁻²Im∂U`; CMP109:
`J_j = D*_{Ũ_j}^{ξ*}ξ⁻²π Im∂U_j`. The differences are exactly the surface-level ones this campaign's
"nine same-name hazards in one day" note warns to check for, and NONE of them survive scrutiny as a
genuine distinct-object difference:
* `η` (CMP99b) vs `ξ` (CMP109) — both papers' own lattice-spacing symbol, nothing more (CMP99b's
  whole apparatus is written in `η`; CMP109 is a later summary paper using `ξ` throughout its own
  text — same role, different letter, exactly like the `Δ`/`Δ_k` naming trap already logged).
* `Im U = (U-U⁻¹)/2i` is stated **identically**, verbatim, in both eq. (3.11)'s surrounding text
  (`(∂U)(p)=U(∂p)`, with `Im` used exactly as `imHolonomy` already builds it in `DeltaPrime.lean`)
  and CMP109 (1.8)'s own explicit clause.
* CMP109 states the `π`-projection onto `𝔤ᶜ` EXPLICITLY; CMP99b's (3.11) does not restate it inline
  on this page — but CMP99b's whole apparatus is built on Lie-algebra-valued (`𝔤ᶜ`-valued, i.e.
  Hermitian-traceless) fields throughout (p.391's own "`A` Hermitian" convention, already logged in
  `DeltaPrime.lean`'s module docstring), so the projection is the SAME operation, present either way
  (CMP109 makes it explicit because it is being pedantic about a `RG`-summary's regularity
  conditions; CMP99b's `J` is built from `D*` applied to `Im∂U`, and `D*`'s own domain in (3.9) is
  already restricted to `𝔤ᶜ`-valued `F`, so the projection there is implicit in the type, not a
  content difference). **This file makes the projection EXPLICIT** (`piProj` below) precisely
  because our carrier is untyped `Matrix (Fin 2) (Fin 2) ℂ`, not a `𝔤ᶜ`-typed subtype — the SAME
  discipline `DeltaPrime.lean` already applies to `suTwo`.
* The `j`-subscript on `J_j`/`U_j` in CMP109 is the RG-STEP index; CMP99b's `J` (used at (3.155)/
  (3.156), which are THEMSELVES about the fixed "step `k`" unit-lattice covariance) is the
  SAME construction specialized to one fixed step — not carrying the index is a notational
  simplification for a single-step paper, not a different object.

**Verdict: SAME OBJECT.** No named divergence found on direct page comparison; this is the
"background/source configuration" `J`, distinct from `g` (the paired test function, already
adjudicated as a SEPARATE object on `corpus/pages/CMP99b_p428.md`, "`J`, not `g`").

## VERDICT 2 — `D̃⁽²⁾` (CMP99b) IS `C̃⁽²⁾` (CMP109), UNDER A DIFFERENT LETTER

CMP99b p.427 states `D̃⁽²⁾(B)` is "similar to `C^{(2)}(A)`, only restricted to unit blocks." CMP109
(1.5)'s own text, independently, describes `C̃^{(2)}(Ū_k^j,B)` as **"the second order polynomial in
the expansion of `Q̃(Ū_k^j,B)`"** — this is EXACTLY the shape CMP99b p.421 uses to describe the
UN-tilded `C^{(2)}(A)` ("a second order term in the expansion of `Q_j(ηA)`"). Two independent papers
in the series describe the SAME construction (a second-order Taylor/expansion coefficient of the
averaging map `Q`/`Q̃`, restricted to unit blocks) under **two different letters** (`D̃` in CMP99b,
`C̃` in CMP109) — precisely the trap this dispatch was fired to catch. **Verdict: same construction,
different symbol across papers; NOT a same-name-different-object hazard (the reverse: a
different-name-same-object one), confirmed by the matching prose description, not merely by
symbol-shape.**

## THE MISSING EXTERNAL PRIMITIVE, NAMED

Both papers, independently, refuse to define the averaging map `Q_j`/`Q̃` in-line. CMP99b p.392,
immediately before (3.13): *"A next class of operators we have to consider is determined by
averaging operators. They were defined in [5], and because the definition is quite long and
complicated we refer the reader to that paper."* CMP99b's own bibliography (`p.434`,
`corpus/mathpix/.../normalized/p434.md`) identifies `[5]` as **"Balaban, T.: 'Averaging operations
for lattice gauge theories.' Harvard preprint HUTMP B147"**. ⚠ **CORRECTED (2026-07-23, Sol+Kimi
triple-prosecution, both image-verified):** `[5]`'s PUBLISHED FORM IS IN THIS CORPUS — it is
`compute/balaban_su2_papers/balaban_CMP98_1985_averaging.pdf` (Bałaban, "Averaging Operations for
Lattice Gauge Theories," Commun. Math. Phys. **98**, 17–51 (1985); title page image-confirmed). The
formulas CMP99b p.392 points at, **(89)–(92)**, are on **CMP98 printed p.31** (image-matched), and
p.433's (3.193) cite of `[5]`'s (61),(78)–(80) is likewise in CMP98. The earlier "CMP89" lead was
WRONG — CMP89 is CMP99b's reference `[2]` ("Regularity and decay of lattice Green's functions"), a
different paper. So `Q_j(U,ηA)` (eq. 3.13), built from the iterated averaging `Ū^j`, is blocked NOT
on an *absent* external primitive but on the **Lean formalization** of CMP98's `Ū^j` — the SOURCE
is on disk, the FORMALIZATION is unbuilt. **`D̃⁽²⁾`/`C̃⁽²⁾`'s CMP99b-specific instantiation is a
NAMED-GAP buildable from held CMP98 material, not an unavailable external gap.**

## WHAT THIS FILE BUILDS INSTEAD

1. **`J`, in full** — CMP99b (3.9)+(3.11)'s EXPLICIT combinatorial formula, built directly (not
   re-derived as an abstract adjoint of anything), reusing `imHolonomy` (`DeltaPrime.lean`, LAW-19)
   and `conjByAmbient` (`CovariantOperators.lean`, LAW-19) for the per-direction transport. Proved
   genuinely nonzero on the tree's own non-flat witness (`witnessU`), and genuinely zero at the flat
   background (`trivialU`) — the same two-sided non-degeneracy pattern `DeltaPrime.lean` §5/§9
   already established for `Δ′`, reused here for consistency, not reinvented.
2. **`D̃⁽²⁾`'s GENERAL SHAPE** — "the second order term in the expansion of `Q`," built as a genuine,
   general, non-degenerate Lean construction (`taylorQuadraticTerm`, the second-derivative-at-`0`
   Taylor coefficient of a curve `t ↦ Q(t•B)`), matching literally what BOTH papers say `D̃⁽²⁾`/`C̃⁽²⁾`
   IS, with the CMP99b-specific `Q` left as the named external parameter (§9's "missing primitive").

## WHAT THIS FILE DOES **NOT** DO

It does not construct Balaban's own `Q_j`/`Ū^j` averaging map (blocked on `[5]`, not in this
corpus). It does not edit `DeltaKRecursive.lean`, `CovariantG1.lean` (`Q`/`G₁`, held by a concurrent
lane), `VariationalProjectorH1.lean` (`H₁`, held by a concurrent lane), or any other existing file
(write-scope discipline). It does not attempt the `Δ_k` assembly itself.
-/

namespace AdalyFormal.Balaban.SourceJ

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.CovariantHjMinimizer

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `π`, the projection onto traceless matrices (CMP109 (1.8)'s own explicit clause,
"the projection ... onto the algebra `𝔤ᶜ`"), made EXPLICIT since this file's carrier is untyped
`Matrix (Fin 2) (Fin 2) ℂ`, unlike `DeltaPrime.lean`'s `suTwo`-typed objects. -/

/-- **`π(X) := X - (tr X / 2)·I`**, the projection of an arbitrary `2×2` complex matrix onto the
traceless subspace (`𝔤ᶜ = 𝔰𝔩(2,ℂ)` for `N=2`) — CMP109 (1.8)'s "projection ... onto the algebra
`𝔤ᶜ`", made concrete for `N=2`. -/
noncomputable def piProj (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  X - (Matrix.trace X / (2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- **`π` is idempotent up to no-op on already-traceless input** — the check that makes `piProj`
non-vacuous: a matrix with nonzero trace is genuinely MOVED by `π`. -/
theorem piProj_eq_self_of_trace_zero {X : Matrix (Fin 2) (Fin 2) ℂ} (h : Matrix.trace X = 0) :
    piProj X = X := by
  unfold piProj
  rw [h]
  simp

theorem piProj_neg (X : Matrix (Fin 2) (Fin 2) ℂ) : piProj (-X) = -piProj X := by
  unfold piProj
  rw [Matrix.trace_neg]
  module

/-- **`π` genuinely acts nontrivially on a matrix with nonzero trace** — the S82-style
falsifiability witness for `piProj` itself: the "garbage" input `(2:ℂ) • (1 : Matrix (Fin 2)(Fin 2)
ℂ)` (trace `4 ≠ 0`) is moved to `0`, not fixed. -/
theorem piProj_two_smul_one :
    piProj ((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  unfold piProj
  have htr : Matrix.trace ((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 4 := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num
  rw [htr]
  norm_num

#print axioms piProj_eq_self_of_trace_zero
#print axioms piProj_neg
#print axioms piProj_two_smul_one

/-! ## §2 — `J`, CMP99b (3.9)+(3.11)'s explicit formula, built directly -/

/-- **`F_{νμ}(y)`**, CMP99b (3.9)'s antisymmetric-extension convention `F_{μν}(x) = -F_{νμ}(x)`,
instantiated at `F := π ∘ imHolonomy U` (i.e. eq. 1.8's `π Im ∂U`, with `η = 1` on the unit
lattice, matching `DeltaPrime.lean`'s own disclosed `ε → 1` convention throughout this file
family). Total on all `(ν,μ) : Fin 3 × Fin 3` via trichotomy; the `ν = μ` branch (never reached by
`Jfield` below, which always supplies `ν ≠ μ`) is fixed at `0` for definitional totality. -/
noncomputable def FnuMu
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) : Matrix (Fin 2) (Fin 2) ℂ :=
  if hlt : ν < μ then piProj (imHolonomy U (y, ⟨(ν, μ), hlt⟩))
  else if hgt : μ < ν then -piProj (imHolonomy U (y, ⟨(μ, ν), hgt⟩))
  else 0

/-- **`D*_ν`, the single-direction transport-difference operator** — CMP99b (3.9)'s own building
block, the SAME combinatorial shape `CovariantHjMinimizer.lean`'s `gradCovariantAdjointValue`
already uses for (3.8) (`R(U(shiftBack·,ν))⁻¹`-transported inflow minus outflow), here applied to a
plaquette-restricted function `G` rather than a bond-component function — matching (3.9)'s own
verbal description of `D*_ν` as the transport-adjoint "in direction `ν`," reused unchanged in
shape, not rebuilt from scratch (`conjByAmbient`, `CovariantOperators.lean`, LAW-19, stands in for
`RMap`'s conjugation here since `imHolonomy`'s values are Hermitian, not skew-Hermitian, hence not
`suTwo`-typed — `conjByAmbient` is already built on the AMBIENT matrix space precisely for this). -/
noncomputable def DstarDir
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν : Fin 3)
    (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ) (x : PeriodicLatticeSite L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  conjByAmbient (U (periodicLatticeShiftBack x ν, ν))⁻¹ (G (periodicLatticeShiftBack x ν)) - G x

/-- **`J(x,μ) := Σ_{ν≠μ} (D*_ν F_{νμ})(x)`**, CMP99b (3.9)'s own final display, applied to
`F := π∘Im∂U` per (3.11)/(1.8). -/
noncomputable def Jfield
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ ν : Fin 3, if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x

/-- **`J`, as a bond-indexed field** — CMP99b (3.11)'s own indexing (`J(b)`, `b ⊂ T_η`). -/
noncomputable def Jsource
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Bond L → Matrix (Fin 2) (Fin 2) ℂ :=
  fun b => Jfield U b.1 b.2

/-! ## §3 — `J` VANISHES at the trivial background, for EVERY bond (fully general, matching
`DeltaPrime.lean` §5's pattern for `Δ′`) -/

theorem FnuMu_trivialU (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMu (DeltaPrime.trivialU (L := L)) ν μ y = 0 := by
  unfold FnuMu
  split_ifs with h1 h2
  · rw [imHolonomy_trivialU]; unfold piProj; simp
  · rw [imHolonomy_trivialU]; unfold piProj; simp
  · rfl

theorem DstarDir_trivialU_eq_zero_of_G_zero (ν : Fin 3)
    (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ) (hG : ∀ y, G y = 0)
    (x : PeriodicLatticeSite L) : DstarDir (DeltaPrime.trivialU (L := L)) ν G x = 0 := by
  unfold DstarDir
  rw [hG, hG]
  simp [conjByAmbient_apply]

theorem Jfield_trivialU (x : PeriodicLatticeSite L) (μ : Fin 3) :
    Jfield (DeltaPrime.trivialU (L := L)) x μ = 0 := by
  unfold Jfield
  apply Finset.sum_eq_zero
  intro ν _
  split_ifs with h
  · rfl
  · exact DstarDir_trivialU_eq_zero_of_G_zero ν _ (fun y => FnuMu_trivialU ν μ y) x

/-- **MANDATE PROPERTY, fully general**: `J` vanishes at the trivial (flat) background, for EVERY
bond and EVERY periodic lattice `L` — not merely on a witness. -/
theorem Jsource_trivialU_eq_zero (b : Bond L) : Jsource (DeltaPrime.trivialU (L := L)) b = 0 :=
  Jfield_trivialU b.1 b.2

#print axioms FnuMu_trivialU
#print axioms DstarDir_trivialU_eq_zero_of_G_zero
#print axioms Jfield_trivialU
#print axioms Jsource_trivialU_eq_zero

/-! ## §4 — `J` IS GENUINELY NONZERO on the tree's own non-flat witness `witnessU`

`witnessU` (`CovariantOperators.lean`, reused unchanged, LAW-19) is nontrivial ONLY on the single
bond `(witnessY,0)`, `witnessMElem` there. Exactly four plaquettes carry nonzero holonomy under it
— `witnessPlaquette`, `myWitnessPlaquette2` (both already shown `= witnessMElem`, `DeltaPrime.lean`
§7) and `p3`, `p4` (both already shown `= witnessMElem⁻¹`, same section) — reused directly, not
recomputed. -/

/-- **`imHolonomy witnessU witnessPlaquette`, in closed form**: `witnessMElem⁻¹ = -witnessMElem`
(as matrices, `DeltaPrime.lean`'s own `witnessMElem_coe_add_inv_coe_eq_zero`), so the two-term
`(1/2i)(hol - hol⁻¹)` collapses to a single multiple of `witnessMElem`. -/
theorem imHolonomy_witnessU_witnessPlaquette_eq :
    imHolonomy witnessU witnessPlaquette =
      !![0, -Complex.I; Complex.I, 0] := by
  unfold imHolonomy
  rw [holonomy_witnessU_witnessPlaquette, holonomyElemInv_witnessU_witnessPlaquette,
    witnessMElem_inv_coe_eq_conjTranspose]
  show (1 / (2 * Complex.I) : ℂ) •
      ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) =
    !![0, -Complex.I; Complex.I, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessMElem, witnessM, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Complex.ext_iff] <;>
    field_simp <;> ring_nf

theorem imHolonomy_witnessU_p3_eq :
    imHolonomy witnessU p3 = !![0, Complex.I; -Complex.I, 0] := by
  unfold imHolonomy
  rw [holonomy_witnessU_p3, holonomyElemInv_witnessU_p3, witnessMElem_inv_coe_eq_conjTranspose]
  show (1 / (2 * Complex.I) : ℂ) •
      ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)ᴴ - (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)) =
    !![0, Complex.I; -Complex.I, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessMElem, witnessM, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Complex.ext_iff] <;>
    field_simp <;> ring_nf

theorem imHolonomy_witnessU_myWitnessPlaquette2_eq :
    imHolonomy witnessU myWitnessPlaquette2 = !![0, -Complex.I; Complex.I, 0] := by
  unfold imHolonomy
  rw [holonomy_witnessU_myWitnessPlaquette2, holonomyElemInv_witnessU_myWitnessPlaquette2,
    witnessMElem_inv_coe_eq_conjTranspose]
  show (1 / (2 * Complex.I) : ℂ) •
      ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) =
    !![0, -Complex.I; Complex.I, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessMElem, witnessM, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Complex.ext_iff] <;>
    field_simp <;> ring_nf

theorem imHolonomy_witnessU_p4_eq :
    imHolonomy witnessU p4 = !![0, Complex.I; -Complex.I, 0] := by
  unfold imHolonomy
  rw [holonomy_witnessU_p4, holonomyElemInv_witnessU_p4, witnessMElem_inv_coe_eq_conjTranspose]
  show (1 / (2 * Complex.I) : ℂ) •
      ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)ᴴ - (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)) =
    !![0, Complex.I; -Complex.I, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessMElem, witnessM, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Complex.ext_iff] <;>
    field_simp <;> ring_nf

#print axioms imHolonomy_witnessU_witnessPlaquette_eq
#print axioms imHolonomy_witnessU_p3_eq
#print axioms imHolonomy_witnessU_myWitnessPlaquette2_eq
#print axioms imHolonomy_witnessU_p4_eq

theorem trace_imHolonomy_witnessU_witnessPlaquette_zero :
    Matrix.trace (imHolonomy witnessU witnessPlaquette) = 0 := by
  rw [imHolonomy_witnessU_witnessPlaquette_eq]
  simp [Matrix.trace_fin_two]

theorem trace_imHolonomy_witnessU_p3_zero :
    Matrix.trace (imHolonomy witnessU p3) = 0 := by
  rw [imHolonomy_witnessU_p3_eq]
  simp [Matrix.trace_fin_two]

theorem trace_imHolonomy_witnessU_myWitnessPlaquette2_zero :
    Matrix.trace (imHolonomy witnessU myWitnessPlaquette2) = 0 := by
  rw [imHolonomy_witnessU_myWitnessPlaquette2_eq]
  simp [Matrix.trace_fin_two]

theorem trace_imHolonomy_witnessU_p4_zero :
    Matrix.trace (imHolonomy witnessU p4) = 0 := by
  rw [imHolonomy_witnessU_p4_eq]
  simp [Matrix.trace_fin_two]

/-- `π` is a no-op on all four exceptional plaquette values (already traceless). -/
theorem piProj_imHolonomy_witnessPlaquette_eq :
    piProj (imHolonomy witnessU witnessPlaquette) = imHolonomy witnessU witnessPlaquette :=
  piProj_eq_self_of_trace_zero trace_imHolonomy_witnessU_witnessPlaquette_zero

theorem piProj_imHolonomy_p3_eq :
    piProj (imHolonomy witnessU p3) = imHolonomy witnessU p3 :=
  piProj_eq_self_of_trace_zero trace_imHolonomy_witnessU_p3_zero

theorem piProj_imHolonomy_myWitnessPlaquette2_eq :
    piProj (imHolonomy witnessU myWitnessPlaquette2) = imHolonomy witnessU myWitnessPlaquette2 :=
  piProj_eq_self_of_trace_zero trace_imHolonomy_witnessU_myWitnessPlaquette2_zero

theorem piProj_imHolonomy_p4_eq :
    piProj (imHolonomy witnessU p4) = imHolonomy witnessU p4 :=
  piProj_eq_self_of_trace_zero trace_imHolonomy_witnessU_p4_zero

#print axioms piProj_imHolonomy_witnessPlaquette_eq
#print axioms piProj_imHolonomy_p3_eq
#print axioms piProj_imHolonomy_myWitnessPlaquette2_eq
#print axioms piProj_imHolonomy_p4_eq

/-- `FnuMu witnessU 1 0 witnessY`, computed: `ν=1 > μ=0`, so the `hgt` branch fires with
`(μ,ν)=(0,1)`, exactly `witnessPlaquette`'s own direction pair. -/
theorem FnuMu_witnessU_1_0_witnessY :
    FnuMu witnessU 1 0 AdmissibleSubspace.witnessY = -imHolonomy witnessU witnessPlaquette := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0:Fin 3) < 1 by decide)]
  show -piProj (imHolonomy witnessU (AdmissibleSubspace.witnessY, ⟨(0, 1), _⟩)) = _
  rw [show (AdmissibleSubspace.witnessY, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) =
      witnessPlaquette from rfl, piProj_imHolonomy_witnessPlaquette_eq]

theorem FnuMu_witnessU_1_0_p3Site :
    FnuMu witnessU 1 0 p3Site = -imHolonomy witnessU p3 := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0:Fin 3) < 1 by decide)]
  show -piProj (imHolonomy witnessU (p3Site, ⟨(0, 1), _⟩)) = _
  rw [show (p3Site, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) = p3 from rfl,
    piProj_imHolonomy_p3_eq]

theorem FnuMu_witnessU_2_0_witnessY :
    FnuMu witnessU 2 0 AdmissibleSubspace.witnessY = -imHolonomy witnessU myWitnessPlaquette2 := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0:Fin 3) < 2 by decide)]
  show -piProj (imHolonomy witnessU (AdmissibleSubspace.witnessY, ⟨(0, 2), _⟩)) = _
  rw [show (AdmissibleSubspace.witnessY, (⟨(0, 2), by decide⟩ : PeriodicPlaquetteDirections)) =
      myWitnessPlaquette2 from rfl, piProj_imHolonomy_myWitnessPlaquette2_eq]

theorem FnuMu_witnessU_2_0_p4Site :
    FnuMu witnessU 2 0 p4Site = -imHolonomy witnessU p4 := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0:Fin 3) < 2 by decide)]
  show -piProj (imHolonomy witnessU (p4Site, ⟨(0, 2), _⟩)) = _
  rw [show (p4Site, (⟨(0, 2), by decide⟩ : PeriodicPlaquetteDirections)) = p4 from rfl,
    piProj_imHolonomy_p4_eq]

#print axioms FnuMu_witnessU_1_0_witnessY
#print axioms FnuMu_witnessU_1_0_p3Site
#print axioms FnuMu_witnessU_2_0_witnessY
#print axioms FnuMu_witnessU_2_0_p4Site

theorem shiftBack_witnessY_1_eq_p3Site :
    periodicLatticeShiftBack AdmissibleSubspace.witnessY 1 = p3Site := by
  rw [← shift_p3Site_eq, periodicLatticeShiftBack_shift]

theorem shiftBack_witnessY_2_eq_p4Site :
    periodicLatticeShiftBack AdmissibleSubspace.witnessY 2 = p4Site := by
  rw [← shift_p4Site_eq, periodicLatticeShiftBack_shift]

theorem conjByAmbient_one_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : conjByAmbient 1 X = X := by
  rw [conjByAmbient_apply]
  simp

/-- **`(D*_1 (F_{1,0}))(witnessY) = imW + imW`** (`imW := imHolonomy witnessU witnessPlaquette`),
stated via ADDITION rather than scalar multiplication to avoid any `ℕ`-smul-on-matrix-entries
ambiguity in the closing computation. -/
theorem DstarDir_1_witnessY :
    DstarDir witnessU 1 (fun y => FnuMu witnessU 1 0 y) AdmissibleSubspace.witnessY =
      imHolonomy witnessU witnessPlaquette + imHolonomy witnessU witnessPlaquette := by
  unfold DstarDir
  dsimp only
  rw [shiftBack_witnessY_1_eq_p3Site, FnuMu_witnessU_1_0_p3Site, FnuMu_witnessU_1_0_witnessY,
    witnessU_at_p3Site_nu, inv_one, conjByAmbient_one_apply]
  rw [imHolonomy_witnessU_p3_eq, imHolonomy_witnessU_witnessPlaquette_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **`(D*_2 (F_{2,0}))(witnessY) = imW + imW`** (the `ν=2` term is the SAME closed value as the
`ν=1` term — both exceptional-plaquette pairs share the identical holonomy `witnessMElem`/
`witnessMElem⁻¹` values, `DeltaPrime.lean` §7). -/
theorem DstarDir_2_witnessY :
    DstarDir witnessU 2 (fun y => FnuMu witnessU 2 0 y) AdmissibleSubspace.witnessY =
      imHolonomy witnessU witnessPlaquette + imHolonomy witnessU witnessPlaquette := by
  unfold DstarDir
  dsimp only
  rw [shiftBack_witnessY_2_eq_p4Site, FnuMu_witnessU_2_0_p4Site, FnuMu_witnessU_2_0_witnessY,
    witnessU_at_p4Site_nu, inv_one, conjByAmbient_one_apply]
  rw [imHolonomy_witnessU_p4_eq, imHolonomy_witnessU_myWitnessPlaquette2_eq,
    imHolonomy_witnessU_witnessPlaquette_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

#print axioms DstarDir_1_witnessY
#print axioms DstarDir_2_witnessY

/-- **THE HEADLINE NON-DEGENERACY WITNESS**: `J(witnessU)(witnessY,0) = imW+imW+imW+imW ≠ 0`
(`imW := imHolonomy witnessU witnessPlaquette = !![0,-i;i,0]`). Built by DIRECT computation of
`Jfield`'s three-term sum over `Fin 3` (`ν=0`: killed by the `if ν=μ` guard; `ν=1,2`: each
`imW+imW`), reusing `DeltaPrime.lean`'s own already-proved holonomy facts throughout, never
recomputing them. -/
theorem Jfield_witnessU_witnessY_0 :
    Jfield witnessU AdmissibleSubspace.witnessY 0 =
      imHolonomy witnessU witnessPlaquette + imHolonomy witnessU witnessPlaquette +
        (imHolonomy witnessU witnessPlaquette + imHolonomy witnessU witnessPlaquette) := by
  unfold Jfield
  rw [Fin.sum_univ_three]
  rw [if_pos rfl, if_neg (by decide : (1:Fin 3) ≠ 0), if_neg (by decide : (2:Fin 3) ≠ 0)]
  rw [DstarDir_1_witnessY, DstarDir_2_witnessY]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem Jfield_witnessU_witnessY_0_ne_zero :
    Jfield witnessU AdmissibleSubspace.witnessY 0 ≠ 0 := by
  rw [Jfield_witnessU_witnessY_0, imHolonomy_witnessU_witnessPlaquette_eq]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp at h01

/-- **MANDATE PROPERTY**: `J`, as a genuine bond-indexed source field, is nonzero at the witness
bond. -/
theorem Jsource_witnessU_ne_zero :
    Jsource witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 0 :=
  Jfield_witnessU_witnessY_0_ne_zero

#print axioms Jfield_witnessU_witnessY_0
#print axioms Jfield_witnessU_witnessY_0_ne_zero
#print axioms Jsource_witnessU_ne_zero

/-! ## §5 — S82 GARBAGE / FALSIFIABILITY: the check CAN fail

Replacing `witnessU` (genuinely non-flat, one non-central `witnessMElem` bond) with `trivialU`
(the mutation an adversary would try first) makes the headline nonzero-witness claim FALSE — the
exact same field, same bond, same construction, but with the background mutated to trivial. -/

theorem Jsource_trivialU_witnessBond_eq_zero :
    Jsource (DeltaPrime.trivialU (L := AdmissibleSubspace.witnessL))
        (AdmissibleSubspace.witnessY, (0 : Fin 3)) = 0 :=
  Jsource_trivialU_eq_zero _

/-- **The falsifiability exhibit**: the SAME statement shape ("`Jsource _ (witnessY,0) ≠ 0`"),
run on the `trivialU` mutation, is FALSE (its negation, `= 0`, holds) — confirming
`Jsource_witnessU_ne_zero` is not a tautology forced by the construction's TYPE alone. -/
theorem Jsource_mutation_breaks_nondegeneracy :
    ¬ (Jsource (DeltaPrime.trivialU (L := AdmissibleSubspace.witnessL))
        (AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 0) := by
  rw [Jsource_trivialU_witnessBond_eq_zero]
  simp

#print axioms Jsource_trivialU_witnessBond_eq_zero
#print axioms Jsource_mutation_breaks_nondegeneracy

/-! ## §6 — `D̃⁽²⁾`'s GENERAL SHAPE: "the second order term in the expansion of `Q`"

Both CMP99b p.421 ("a second order term in the expansion of `Q_j(ηA)`") and CMP109 p.261 ("the
second order polynomial in the expansion of `Q̃(Ū_k^j,B)`") describe `C^{(2)}`/`D̃^{(2)}`/`C̃^{(2)}`
identically: the SECOND-ORDER TAYLOR COEFFICIENT of an averaging map `Q`, in its argument. This
section builds that extraction operation in general (any real normed space `E`, any curve
`Q : ℝ → E`), independent of what `Q` itself is — CMP99b's OWN specific `Q_j` (eq. 3.13, built from
the iterated averaging operation `Ū^j`) is the missing external primitive (module docstring,
"THE MISSING EXTERNAL PRIMITIVE"), never assumed available here. -/

/-- **`taylorQuadraticTerm Q := (1/2)·Q''(0)`** — the coefficient of `t²` in
`Q(t) = Q(0) + t·Q'(0) + (t²/2)·Q''(0) + o(t²)`, i.e. literally "the second order term in the
expansion of `Q`." -/
noncomputable def taylorQuadraticTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ℝ → E) : E :=
  (1 / 2 : ℝ) • deriv (deriv Q) 0

/-- **Non-degeneracy witness**: for the genuinely-quadratic curve `Q(t) = t²`, the extracted
coefficient is `1 ≠ 0` — the construction does real work, not vacuous by type alone. -/
theorem taylorQuadraticTerm_sq : taylorQuadraticTerm (fun t : ℝ => t ^ 2) = 1 := by
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    have : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t ^ 1) t := by
      simpa using hasDerivAt_pow 2 t
    simpa [mul_comm] using this.deriv
  rw [h1]
  have h2 : deriv (fun t : ℝ => 2 * t) 0 = 2 := by
    have : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    simpa using this.deriv
  rw [h2]
  norm_num

#print axioms taylorQuadraticTerm_sq

/-- **S82 GARBAGE SUBSTITUTION**: the LINEAR curve `Q(t) = t` (a curve with NO genuine second-order
content — "garbage" relative to what a quadratic-term extractor should report) makes the extracted
coefficient `0` — the check on `taylorQuadraticTerm_sq` is not forced by the construction's type;
a curve with the WRONG shape (linear instead of quadratic) genuinely breaks the "nonzero" reading. -/
theorem taylorQuadraticTerm_linear : taylorQuadraticTerm (fun t : ℝ => t) = 0 := by
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => t) = fun _ => (1 : ℝ) := by
    funext t; simp
  rw [h1]
  simp

#print axioms taylorQuadraticTerm_linear

/-- **`taylorQuadraticTerm` genuinely depends on `B` through a parametrized curve** — the shape
`D̃⁽²⁾(B)`/`C̃⁽²⁾(·,B)` actually needs (a QUADRATIC FORM in `B`, not a fixed number): given any
`Q : H → E` and direction `B : H`, `Dtilde2Shape Q B := taylorQuadraticTerm (fun t => Q (t • B))`. -/
noncomputable def Dtilde2Shape {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : H → E) (B : H) : E :=
  taylorQuadraticTerm (fun t : ℝ => Q (t • B))

/-- **Witness**: for `Q(v) = ‖v‖_1²`-style quadratic `Q(x) = x * x` on `H := ℝ`, `Dtilde2Shape Q B
= B * B`, a genuine quadratic (NOT linear, NOT constant) function of `B`, matching literally
"a quadratic polynomial in `B`" (CMP99b p.427's own description of `D̃⁽²⁾`). -/
theorem Dtilde2Shape_sq (B : ℝ) :
    Dtilde2Shape (fun x : ℝ => x * x) B = B * B := by
  unfold Dtilde2Shape
  have heq : (fun t : ℝ => (t • B) * (t • B)) = fun t : ℝ => (B * B) * t ^ 2 := by
    funext t; simp [smul_eq_mul]; ring
  rw [heq]
  have : taylorQuadraticTerm (fun t : ℝ => (B * B) * t ^ 2) = B * B := by
    unfold taylorQuadraticTerm
    have h1 : deriv (fun t : ℝ => (B * B) * t ^ 2) = fun t => (B * B) * (2 * t) := by
      funext t
      have hbase : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t ^ 1) t := by
        simpa using hasDerivAt_pow 2 t
      have := (hbase.const_mul (B * B))
      simpa [mul_comm, mul_left_comm, mul_assoc] using this.deriv
    rw [h1]
    have h2 : deriv (fun t : ℝ => (B * B) * (2 * t)) 0 = (B * B) * 2 := by
      have : HasDerivAt (fun t : ℝ => (B * B) * (2 * t)) ((B * B) * 2) 0 := by
        have hb : HasDerivAt (fun t : ℝ => (2:ℝ) * t) 2 (0:ℝ) := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
        simpa [mul_comm] using hb.const_mul (B * B)
      simpa using this.deriv
    rw [h2]
    ring
  rw [this]

#print axioms Dtilde2Shape_sq

/-- **S82 GARBAGE for `Dtilde2Shape`**: the LINEAR `Q(x) = c*x` gives `Dtilde2Shape Q B = 0`
identically in `B` — a genuinely different, FALSE reading of "quadratic in `B`" relative to
`Dtilde2Shape_sq`, confirming the construction is sensitive to `Q`'s actual second-order content,
not merely its type. -/
theorem Dtilde2Shape_linear (c B : ℝ) :
    Dtilde2Shape (fun x : ℝ => c * x) B = 0 := by
  unfold Dtilde2Shape
  have heq : (fun t : ℝ => c * (t • B)) = fun t : ℝ => (c * B) * t := by
    funext t; simp [smul_eq_mul]; ring
  rw [heq]
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => (c * B) * t) = fun _ => c * B := by
    funext t
    have : HasDerivAt (fun t : ℝ => (c * B) * t) (c * B) t := by
      simpa using (hasDerivAt_id t).const_mul (c * B)
    simpa using this.deriv
  rw [h1]
  simp

#print axioms Dtilde2Shape_linear

/-! ## §7 — RESIDUALS, NAMED PRECISELY (mechanical propagation target)

1. **`Dtilde2Shape`'s CMP99b-specific instantiation** — substituting `Q := Q_j(U,η·)` (eq. 3.13)
   for the abstract `Q` above is BLOCKED on Balaban's own deferred averaging-operator construction
   `[5]` ("Averaging operations for lattice gauge theories," Harvard preprint HUTMP B147), not
   rendered/ingested anywhere in this corpus (a lead, NOT a confirmed identification: this
   campaign's `CMP89` render, `compute/how_he_proves_it/renders/CMP89_pdfpg16-16.png`, is a
   plausible candidate for `[5]`'s published form, unconfirmed here). Until `[5]`'s `Ū^j`
   construction is built, `Dtilde2Shape (Q_j U η·) B` cannot be literally instantiated.
2. **`Jsource`'s Hermitian-vs-`suTwo` convention** — `Jsource` returns `Matrix (Fin 2) (Fin 2) ℂ`
   values (Balaban's OWN Hermitian `𝔤ᶜ` convention, matching `A`'s convention per `DeltaPrime.lean`'s
   module docstring), not `SuTwo` (this tree's anti-Hermitian carrier). Plugging `Jsource` into a
   `SuTwo`-typed `H` (e.g. `DeltaKRecursive.RGScaleFamily.J : ℕ → H` with `H := BondFnL2 L`) would
   need the SAME `φ : X ↦ iX` transport `DeltaPrime.lean` already flags for `A`/`Δ′` — NOT applied
   here, named instead, exactly as that file's own precedent.
3. ~~**`Jsource`'s dependence on `U` only (no `k`-indexing)** — CMP99b's own (3.155)/(3.156) use `J`
   at a FIXED renormalization step; `DeltaKRecursive.RGScaleFamily.J : ℕ → H` carries a `k`-index
   this file does not supply (Balaban's own `J`, per CMP109 (1.8), is genuinely `J_j`, `k`-indexed
   THROUGH `U_j` — a family `fun k => Jsource (U_k)` would supply the index once a `k ↦ U_k`
   renormalization-step configuration family exists elsewhere in the tree; none is built here).~~
   **CLOSED 2026-07-29 (`SourceJFaithful.lean`).** The index exists and is populated:
   `SourceJFaithful.UFaithfulSourceIngredients.Jof : ℕ → Uconfig → AnchoredBondSpace Lat`, and
   `SourceJFaithful.faithfulJof` instantiates it as
   `fun _ U => JsourceReal imEntry01 (cond U witnessU trivialU)` — `Jsource` applied to two genuine
   `SU(2)` configurations, with `Jsource_trivialU_eq_zero`/`Jsource_witnessU_ne_zero` supplying the
   proof that the resulting family is non-constant. The residual as written asked for the WRONG
   index: the diagnosis above treats `k` as what is missing, and the load-bearing missing index is
   the CONFIGURATION one. `SourceJFaithful.no_kIndexed_J_realizes_faithful_source` proves the
   `ℕ → H` shape (this residual's own target) cannot realize a `U`-varying source no matter how the
   `k`-index is filled.

## §8 — `Jsource`'S CONSUMER (added 2026-07-29)

Until 2026-07-29 `Jsource` had ZERO external callers — the tree's only faithful `J(U)` was an
island while two other interfaces carried a `U`-blind `J`. `Balaban/SourceJFaithful.lean` is its
first consumer: `SourceJFaithful.JsourceReal` transports it to the goal's own carrier
`Anchoring.AnchoredBondSpace L` and `SourceJFaithful.faithfulSI` uses the result as the `Jof` field
of a fully-discharged (3.156)/(3.157) ingredient set. The transport is LOSSY — see residual 2, whose
`φ : X ↦ iX` diagnosis is refined there: on this carrier no injective map exists at all
(`8·|Bond L|` real dimensions into `|Bond L|`), so the fix is the `su(2)`-valued carrier, not a
better functional.
-/

end AdalyFormal.Balaban.SourceJ
