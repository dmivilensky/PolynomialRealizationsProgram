# Proof dependencies

The complete checks select declarations by their defining module, including
private declarations and generated names outside the article namespace.
They inspect types and proof bodies directly and compare that result with
Lean's stored transitive axiom report. Every article source must be imported.

The proofs of 2606.16671v2 and 2610.05164v2 use:

| Axiom | Meaning |
| --- | --- |
| `propext` | Propositional extensionality |
| `Classical.choice` | Classical choice |
| `Quot.sound` | Equality of quotient classes |

The imported environment also declares the following axioms/runtime primitives.
Their presence is distinct from their use by a mathematical proof; the audit
rejects any dependency on them.

| Imported declaration | Role |
| --- | --- |
| `sorryAx` | Placeholder for an unfinished proof |
| `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` | Compiler/native reduction trust mechanisms |
| `isScalarObj`, `lcAny`, `lcCast`, `lcErased`, `lcProof`, `lcUnreachable`, `lcVoid`, `Quot.lcInv` | Runtime/compiler primitives |

`Numerics/EnergyWitnessGenerator` in 2606.16671v2 contains an automatically
created unsafe runtime helper for witness proposals. The audit permits unsafe
code only in that module, reports its names, and audits all its safe outputs.
The tactic proposes literal integer intervals, adds safe data definitions,
constructs kernel-reduction proofs of their acceptance, and composes those proofs.
No mathematical theorem can depend on the unsafe helper. External Python
proposals for 2610.05164v2 are treated the same way: only kernel-checked
arithmetic and proved ODE/quadrature bounds enter the final theorem.

`Scripts/Replay.lean` is an optional executable using Lean's stock kernel replay;
it is not imported by either mathematical library. Elaborators, audits and
witness proposal code are tooling, not added mathematical axioms.
