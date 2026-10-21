# Compact statement of Balaban's p. 428 coercivity lemma

The frozen encoding
([BalabanCoercivityStatement](https://github.com/elmismisimoxhunca/BalabanCoercivityStatement))
is the single proposition `AdalyFormal.StatementLaneG.P428Target8`. Stating it imports **273 modules, 169 437 lines, 7 762 theorems**, because the operators are defined inside the proof development (Weitzenböck, block Poincaré, the whole renormalisation tower).

This directory is a referee-facing rewrite of that statement for dimension 3 and gauge group SU(2). It keeps the frozen readings (statement sheet, clauses A1–A13) and deletes the proof cone.

| File | What a referee checks |
|---|---|
| `BalabanCompact/Basic.lean` | Torus, periodic `ℓ¹` distance, SU(2) chart `i v·σ`, closed-form `exp` and principal `log`, gauge transform, covariant gradient and curl. |
| `BalabanCompact/Group.lean` | `(i v·σ)² = −‖v‖² I` and the Pauli multiplication table. |
| `BalabanCompact/Class.lean` | `Admissible`, `TorusOK`, `LambdaOK2`, class cubes of factor `f`, `(3.35)`–`(3.36)` in curl form, plaquette-and-site coverage `ClassCoupled`, touching test fields `B̃`. |
| `BalabanCompact/Form.lean` | CMP98 (43) and (63) block averaging, per-component jets `Q` and `C⁽²⁾` (`fderiv` of each bond, the r8 repair), plaquette formula for `Δ'` with normalised trace `tr = ½ Tr`, summed on `plaqIn`. |

Build (Lean v4.31.0, mathlib `v4.31.0`):

```
cd compact && lake exe cache get && lake build
```

## Headline, in the frozen quantifier order

\[
\begin{align*}
&\forall \ell\ge 2\ \forall a>0\ \exists m_0\ge 1\ \forall m\ge m_0\ \exists R_0\ \forall R\ge R_0\\
&\quad \exists a_0>0\ \exists \gamma_0>0\ \forall k\ge 1\ \forall L_u\ \forall \alpha_0>0 \text{ with } 12 M\alpha_0\le a_0,\\
&\qquad M=\ell^m,\ \eta=\ell^{-k}:\\
&\quad\text{if }\operatorname{TorusOK}(\ell,M,L_u),\ 
  \operatorname{Admissible}(\ell,M,R,k,S),\ 
  \operatorname{LambdaOK2}(\ell,M,R,k,S,\Lambda),\\
&\qquad \operatorname{ClassCoupled}(\ell,M,12,k,S,\alpha_0,\eta,U),\\
&\quad\text{then for every admissible }\tilde B:\\
&\qquad \gamma_0\sum_b\|\tilde B(b)\|^2 \le \operatorname{genForm}(C\tilde B).
\end{align*}
\]

`genForm(B) = \eta\langle \tau^* B,(QG_1 Q^*)^{-1}\tau^* B\rangle - a\langle B,B\rangle - 2\langle H_1\tilde D^{(2)}(B), J\rangle`, with `Ring.inverse = 0` off the invertible set.

## Headline in Lean

`BalabanCompact.P428Target8` is in `BalabanCompact/Target.lean`. `genForm` in `BalabanCompact/Ops2.lean` is

`η ⟨τ* B, (Q G₁ Q*)⁻¹ τ* B⟩ − a ⟨B, B⟩ − 2 ⟨H₁ D̃⁽²⁾(B), J⟩`.

`Ops.lean` and `Ops2.lean` build `G'`, `R`, `Δ`, `J`, `G⁻¹`, `G₁⁻¹`, `H₁` and `C = id − h Q₁`. `lake build` in this directory exits 0. This is a second encoding of the frozen headline, not a definitional `rfl` against `AdalyFormal.StatementLaneG.P428Target8`.

## Checked equivalence

The seven statement modules are unchanged. The separate [dictionary project](dictionary/README.md), with 18 proof modules, now establishes:

```lean
CompactDictionary.p428Target8_iff :
  BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8
```

To check it, run `lake exe cache get`, `lake build`, and `lake env lean Check.lean` from `compact/dictionary/`. All its dependencies are public in this repository or pinned third-party packages. The theorem transports the definitions, rather than assuming the two headlines. Its axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The private coercivity proof can therefore be transported to the compact proposition; that application has been checked privately. The full coercivity proof is not distributed in this repository.
