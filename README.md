# Balaban's coercivity lemma: compact statement and checked equivalence

This repository contains a Lean 4 formal statement of the lower bound on p. 428 of T. Balaban, "Propagators for lattice gauge theories in a background field", Commun. Math. Phys. 99 (1985) 389–434, for dimension 3 and gauge group SU(2). It contains a seven-module compact statement, the earlier formal encoding, and a Lean-checked dictionary proving that the two propositions are equivalent. The full coercivity proof is not included in this public referee package.

In Balaban's notation the claim is that the quadratic form

  ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B, Δ_k B⟩   (3.156)

restricted to the constrained fields B = C B̃ satisfies C*Δ_k C ≥ γ₀ > 0, with γ₀ independent of the renormalisation level k and of the background field U in the regularity class (3.35)–(3.36).

## What to read

The statement a referee can check is `compact/`. It is 7 Lean modules. The proposition is `BalabanCompact.P428Target8` in `compact/BalabanCompact/Target.lean`. Build it with `lake build` from `compact/`.

`lean/src/` is the earlier encoding of the same headline. Stating it imports 273 modules because the operators were defined inside a proof development. The seven compact statement modules are unchanged; a separate 18-module dictionary in `compact/dictionary/` now proves:

```lean
CompactDictionary.p428Target8_iff :
  BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8
```

This is a proved equivalence, not a definitional `rfl`. It transports the hypotheses, operators, quadratic form, constants, and quantifier order. It does not assume either headline or import the private coercivity theorem. Its axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.

**Reading scope:** 7 modules for the compact statement; 18 more for the dictionary; the dictionary's full local import closure contains 298 modules (273 earlier encoding + 7 compact + 18 dictionary). `Check.lean` is a separate verification entry point.

**Proof availability:** in the private proof development, `AdalyFormal.M2RightInv.p428Target8` proves the earlier proposition. Applying the public dictionary's `.mpr` direction yields the compact proposition. That private discharge has been Lean-checked, but neither `RI6.lean` nor its full proof dependencies are distributed here. This repository independently checks the equivalence, not the full coercivity proof.

## Contents

| Path | Content |
|---|---|
| `compact/BalabanCompact/` | The unchanged 7-module statement. Start at `compact/README.md` and `compact/BalabanCompact/Target.lean`. |
| `compact/dictionary/` | The 18-module equivalence proof, separate Lake project, and `Check.lean` for the exact theorem type and axiom audit. |
| `sheet/sheet.pdf` | A 7-page comparison of the formal statement with the printed text, clause by clause: the printed sentence, the Lean definition, a plain translation, any deviation, and a yes/no question for the reader. It ends with the statement in ordinary notation and the list of readings that were chosen. |
| `lean/src/ZT5A.lean` | The statement, `AdalyFormal.StatementLaneG.P428Target8` (line 291). |
| `lean/src/` | The 273 modules needed to state it (definitions of the lattice, the tower of domains, the class of cubes, regularity, and the operators). |
| `lean/Statement.lean` | Prints the statement and every definition it uses. Its output is in `lean/statement_output.txt`. |

## Building

Requires `elan`. Each project pins Lean v4.31.0 and mathlib v4.31.0. From the repository root:

```sh
# Read/check just the seven-module compact statement:
cd compact
lake exe cache get
lake build

# Check the dictionary against the earlier encoding, using only this repository:
cd dictionary
lake exe cache get
lake build
lake env lean Check.lean
```

The final command checks the exact equivalence and prints its axiom dependencies. The dictionary uses relative local dependencies on `compact/` and `lean/`; no private repository is required. Its build is larger than the compact-only check because it includes the earlier encoding.

To inspect the earlier statement separately, from `lean/` run:

```sh
lake exe cache get
lake build
lake env lean Statement.lean
```

Lean v4.31.0, mathlib at the revision pinned in `lean/lake-manifest.json`. The modules contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `extern`.

## What to check

The formal equivalence of the compact and earlier propositions is now proved in this package. The separate interpretation question for refereeing remains: does `P428Target8` say what p. 428 says? The sheet lists every clause and every reading; the main points a reader may want to judge are the reading of the lattice T₁ on p. 396, the choice of the level-zero domain Ω₀, the coverage condition on the class of cubes, the set of plaquettes in Δ and J, and the bond convention ("both endpoints" in the class versus "at least one end-point" in CMP 102 p. 277).

## License

Creative Commons Attribution-ShareAlike 4.0 International (CC BY-SA 4.0). See `LICENSE`.
