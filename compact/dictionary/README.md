# Checked dictionary: compact ↔ earlier statement

This directory contains **18 proof modules**: `CompactDictionary.lean` and 17 helper modules in `CompactDictionary/`. The separate `Check.lean` is a verification entry point, not part of that library count.

```lean
CompactDictionary.p428Target8_iff :
  BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8
```

The theorem proves equivalence by transporting the definitions. It does not assume either proposition, import `RI6`, or reprove the coercivity estimate. The seven compact statement modules remain in `../BalabanCompact/`, unchanged.

## Build and check

From this directory, with `elan` installed:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

The project uses the public local packages `../../lean` and `..`; all local dependencies are in this repository. Lean and mathlib are pinned to v4.31.0. The full local import closure is 298 modules: 273 earlier-encoding modules, 7 compact modules, and 18 dictionary modules. Checking only the compact statement remains possible by building `compact/` without this project.

`Check.lean` checks the exact equivalence type and prints its axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

No private repository, coercivity proof, added axiom, or `sorry` is needed for this equivalence.

## Dictionary guide

| Modules | Correspondence |
|---|---|
| `Coordinates`, `Charts` | Pauli coordinate permutation, intrinsic linear isometry, matrix Frobenius factor, total exponential/logarithm including branch and junk values. |
| `Geometry` | Towers, admissibility, torus divisibility, class/coverage, support and test-field hypotheses. |
| `RawStep`, `Jets` | Background blocking, the single-background `qStep`, and first/second per-component derivatives, including nondifferentiability junk. |
| `Corridor`, `LocalForms` | Guarded `C = id - h Q1`, localized plaquette formulas, Δ/J and all six commutator signs. |
| `Padding`, `Transport`, `SiteOperators`, `Delta`, `BondOperators`, `Support` | Full-space versus supported-space identification, adjoints, site/bond operators and masks. |
| `Propagators`, `CorrectedPropagators` | Total inverses, singular branches and corrected propagator correspondence. |
| `Parameters`, `Form` | Hypotheses and exact `genForm` equality, including constants and norm factors. |
| `CompactDictionary.lean` | Instance inequalities, quantifiers and the final `p428Target8_iff`. |

In particular, `qStep` still passes `suExpM (a b)` to `rawStep`, which inserts the background once. The dictionary retains `plaqIn Ω₀`, the zero branch of `Ring.inverse`, and the guarded zero choice for nonbijective `H0`; it does not impose extra invertibility assumptions on the headline.

## Relation to the private proof

The existing private theorem has type:

```lean
AdalyFormal.M2RightInv.p428Target8 : AdalyFormal.StatementLaneG.P428Target8
```

In that private development, the compact theorem is obtained by:

```lean
CompactDictionary.p428Target8_iff.mpr AdalyFormal.M2RightInv.p428Target8
```

That application has been Lean-checked there. The private theorem and its dependencies are **not included** here. The snippets in this section explain the connection; they are not an independently buildable public proof of coercivity. The public deliverable is the checked equivalence between the two formal statements.
