# Continuation: compact statement of Balaban's p. 428 lemma

Written for another machine. Do not restart the cancelled equivalence workflow.

## What is where

Public, for a referee to read:

https://github.com/elmismisimoxhunca/BalabanCoercivityStatement

Commit `d5376ef` on `main`. The statement to show is `compact/` (7 modules, about 1,640 lines). The proposition is `BalabanCompact.P428Target8` in `compact/BalabanCompact/Target.lean`. The older encoding, 273 modules, is still under `lean/src/` in that same repository. They are not connected by `rfl`.

Private proof repository, this checkout:

https://github.com/elmismisimoxhunca/BalabanCoercivityLemma

About 2,762 Lean modules. The theorem `AdalyFormal.M2RightInv.p428Target8` in `lean/src/RI6.lean` proves `AdalyFormal.StatementLaneG.P428Target8`. It does not prove `BalabanCompact.P428Target8`. Do not push this repository. It contains `sources/`.

## What the compact text is

A second writing of the printed lower bound on p. 428 of Balaban, CMP 99 (1985) 389–434, dimension 3, gauge group SU(2). The quadratic form is (3.156). The quantifier order is: `ℓ ≥ 2` and `a > 0`, then `m₀`, then `R₀`, then `a₀ > 0` and `γ₀ > 0`, then `k ≥ 1`, with `M = ℓ^m` and cube factor 12. `Ring.inverse` is 0 off the units. `C = id - h Q₁`, and `h = 0` when `H₀` is not bijective. `Δ` and `J` sum over `plaqIn Ω₀`. The unit background is the k-fold blocked field.

`qStep` must pass `suExpM (a b)` into `rawStep`. `rawStep` multiplies by `V₀` once. An earlier draft passed `exp(a) * V₀` as well, which differentiated the jets at the wrong point and made the headline false. That is fixed in `d5376ef`.

## What a referee check does, and what it does not

Checking `compact/` checks the claim. It does not check the proof. The proof establishes the frozen proposition only. Accepting the short text does not transfer to `p428Target8`, and accepting `p428Target8` does not by itself mean the printed sentence was proved, unless the frozen proposition means that sentence.

The only bridge that would make those the same check is a theorem

`BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8`

and then the existing `p428Target8`. That is a dictionary (hypotheses, the Pauli isometry, exp and log, then `genForm`), not a second coercivity proof. It was started and then stopped. Do not launch it as a multi-agent workflow on a machine that cannot carry the lemma build.

## Stopped work, left in this checkout only

Workflow `compact-equiv` (`wfr_3bd81b16-3aca-4e8b-ab26-3595072a9314`) was cancelled during the dictionary step. It is not to be resumed.

Uncommitted, and not on the public repository:

- `lean/src/CompactEquiv.lean` (13 lines). Imports both headlines. States no theorem.
- `lean/src/BalabanCompact/` copy of the compact modules, made so one Lake project could see both.
- A small addition at the bottom of `lean/lakefile.toml`.
- `.bb/workflows/` (the orchestration scripts).
- `compact/` is untracked here, but the same files are what `d5376ef` published.

Do not commit those into the private lemma repository unless the owner asks. Do not copy `sources/` or the proof tree onto the public statement repository.

## Audits already done

- Kimi K3 acquitted an earlier draft, then the `qStep` bug was found later. Do not treat that acquittal as covering the fixed text.
- GPT 6 Astra convicted the double-background `qStep`. After the fix, Astra returned qualified: no blocking mismatch; remaining items are the Frobenius factor `√2` in the class bounds, junk values, and full-space padding versus the subtype `E₀`.
- Claude Opus 5.5 acquitted the fixed text and reported a scratch comparison. That comparison is not a checked-in Lean proof.
- One later Kimi audit call produced no report.

## Prompt

Paste the following as the first message on the other machine. Point the checkout at the public statement repository if the task is to show or polish the claim. Point it at the private lemma repository only if the task is the dictionary, and only on a machine that can build that project.

```
Read compact/CONTINUATION.md before doing anything.

The public repository is https://github.com/elmismisimoxhunca/BalabanCoercivityStatement at commit d5376ef. The claim a referee reads is compact/, proposition BalabanCompact.P428Target8. The private proof repository BalabanCoercivityLemma proves AdalyFormal.StatementLaneG.P428Target8 only, by AdalyFormal.M2RightInv.p428Target8 in lean/src/RI6.lean. Those two propositions are not identified by a theorem.

Do not resume or restart workflow compact-equiv. Do not fan out agents onto the 2762-module proof. Do not push the private repository and do not publish sources/.

qStep is already fixed: rawStep receives suExpM (a b), and multiplies by V0 once. Do not revert that.

If the task is to show the claim, stay in the public repository and edit only compact/. If the task is to connect the claim to the proof, work in the private repository and prove BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8 by a dictionary (hypotheses, Pauli isometry, exp and log including the branch cut, then genForm). Name qStep's basepoint, plaqIn for Delta and J, the six commutator signs, C = id - h Q1, Ring.inverse = 0, and the E0 padding. Then discharge the compact proposition from p428Target8. Do not rebuild the coercivity estimate. Do not declare that theorem with sorry.
```
