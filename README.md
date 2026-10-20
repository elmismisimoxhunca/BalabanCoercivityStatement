# Balaban's coercivity lemma: the formal statement

This repository contains a Lean 4 formal statement of the lower bound on p. 428 of T. Balaban, "Propagators for lattice gauge theories in a background field", Commun. Math. Phys. 99 (1985) 389–434, for dimension 3 and gauge group SU(2). It contains the statement only, so that it can be checked against the printed text.

In Balaban's notation the claim is that the quadratic form

  ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B, Δ_k B⟩   (3.156)

restricted to the constrained fields B = C B̃ satisfies C*Δ_k C ≥ γ₀ > 0, with γ₀ independent of the renormalisation level k and of the background field U in the regularity class (3.35)–(3.36).

## What to read

The statement a referee can check is `compact/`. It is 7 Lean modules. The proposition is `BalabanCompact.P428Target8` in `compact/BalabanCompact/Target.lean`. Build it with `lake build` from `compact/`.

`lean/src/` is the earlier encoding of the same headline. Stating it imports 273 modules because the operators were defined inside a proof development. It is kept so the two readings can be compared. They are not tied by a definitional `rfl`.

## Contents

| Path | Content |
|---|---|
| `compact/` | The 7-module statement. Start at `compact/README.md` and `compact/BalabanCompact/Target.lean`. |
| `sheet/sheet.pdf` | A 7-page comparison of the formal statement with the printed text, clause by clause: the printed sentence, the Lean definition, a plain translation, any deviation, and a yes/no question for the reader. It ends with the statement in ordinary notation and the list of readings that were chosen. |
| `lean/src/ZT5A.lean` | The statement, `AdalyFormal.StatementLaneG.P428Target8` (line 291). |
| `lean/src/` | The 273 modules needed to state it (definitions of the lattice, the tower of domains, the class of cubes, regularity, and the operators). |
| `lean/Statement.lean` | Prints the statement and every definition it uses. Its output is in `lean/statement_output.txt`. |

## Building

Requires `elan`. From `lean/`:

```
lake exe cache get
lake build
lake env lean Statement.lean
```

Lean v4.31.0, mathlib at the revision pinned in `lean/lake-manifest.json`. The modules contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `extern`.

## What to check

The question this repository is for: does `P428Target8` say what p. 428 says? The sheet lists every clause and every reading; the main points a reader may want to judge are the reading of the lattice T₁ on p. 396, the choice of the level-zero domain Ω₀, the coverage condition on the class of cubes, the set of plaquettes in Δ and J, and the bond convention ("both endpoints" in the class versus "at least one end-point" in CMP 102 p. 277).

## License

Creative Commons Attribution-ShareAlike 4.0 International (CC BY-SA 4.0). See `LICENSE`.
