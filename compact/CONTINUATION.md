# Continuation: public compact statement and checked dictionary

## Current referee package

Public repository: https://github.com/elmismisimoxhunca/BalabanCoercivityStatement

- `compact/BalabanCompact/`: the unchanged **7-module** statement; headline `BalabanCompact.P428Target8`.
- `lean/src/`: the earlier **273-module** encoding; headline `AdalyFormal.StatementLaneG.P428Target8` in `ZT5A.lean`.
- `compact/dictionary/`: **18 dictionary proof modules**, a separate Lake project, and `Check.lean`.

The dictionary now proves:

```lean
CompactDictionary.p428Target8_iff :
  BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8
```

The earlier warning that these propositions had no proved bridge is superseded. They are provably equivalent, not definitionally identical. The dictionary does not import `RI6`, assume either headline, or rebuild the coercivity estimate. Its complete local import closure has 298 modules, all present in this public repository.

## What is public and what remains private

The private `BalabanCoercivityLemma` development proves the earlier proposition by `AdalyFormal.M2RightInv.p428Target8` in `lean/src/RI6.lean`. The compact theorem has also been checked there, with body:

```lean
CompactDictionary.p428Target8_iff.mpr AdalyFormal.M2RightInv.p428Target8
```

Both the equivalence and the private compact theorem have axiom dependencies exactly `[propext, Classical.choice, Quot.sound]`. Focused source checks reused existing frozen dependency caches; no cold rebuild of the entire private proof is claimed.

The full coercivity proof, `RI6.lean`, `CompactCoercivity.lean`, and their private-only dependencies are **not part of this public package**. Never publish `sources/`, unrelated private work, or the private proof tree without explicit authorization. The public dictionary is independently checkable without access to that private repository.

## Build

For the seven-module statement, from `compact/`:

```sh
lake exe cache get
lake build
```

For the equivalence, from `compact/dictionary/`:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

See `dictionary/README.md` for the dictionary map and the distinction between public equivalence and private proof discharge.

## Invariants to preserve

- `qStep` passes `suExpM (a b)` to `rawStep`; `rawStep` multiplies by the background exactly once. Do not restore the old double-background bug.
- The Pauli coordinate permutation and Frobenius norm factor are explicit.
- Total exp/log branches, derivative junk values, `plaqIn Ω₀`, all six commutator signs, and the blocked unit background are preserved.
- `C = id - h Q1`, with `h = 0` for nonbijective `H0`.
- `Ring.inverse = 0` off units; full-space versus supported-space padding must preserve singular branches.
- Hypotheses, constants and quantifier order are transported without weakening the headline.
- Do not add `sorry`, new axioms, or circular equivalence arguments.

## Historical workflow restrictions

The old `compact-equiv` workflow was cancelled and must not be resumed or restarted. The successful dictionary was produced by a separate sequential Astra pipeline and independently verified. Do not fan out workers over the full private proof or transfer work to the old `DESKTOP-9BKM69O` machine.

The proved equivalence answers whether the two Lean statements agree. Fidelity to Balaban's printed text remains a separate referee interpretation question; the older audit opinions are not substitutes for checking that question.
