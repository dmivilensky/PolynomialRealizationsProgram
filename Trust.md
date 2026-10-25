# Proof trust

The proofs in `chebyshev1`, `chebyshev2` and `polyak` permit only three
transitive axioms: `propext`, `Classical.choice` and `Quot.sound`.
Dependencies on `sorryAx`, native reduction axioms and other runtime axioms
are rejected. An axiom's presence in the imported environment does not mean
the proofs use it.

The shared [audit](Tools/Verification/Audit.lean) checks every declaration
owned by the package's modules, including private and generated declarations.
It verifies that every Lean source is imported and compares Lean's axiom
report with a direct traversal of types and proof bodies.

Unsafe declarations are rejected except for one generated witness-proposal
helper in `chebyshev1.Numerics.EnergyWitnessGenerator`, explicitly allowed by
[its check](chebyshev1/Check.lean). Its proposed data and proofs are checked
by the kernel; mathematical theorems cannot depend on the unsafe helper.

Python computations and numerical solvers propose certificate data.
Lean checks the exact arithmetic and its connection to the source formulas.
Archive hashes establish byte identity, not mathematical validity; Polyak's
archive readers accept JSON data and never execute archive-supplied code.

Optional [kernel replay](Tools/Verification/Replay.lean) rechecks compiled
declarations using Lean's kernel against their external dependencies.
Correspondence between the formal statements and the articles requires
mathematical review in addition to compilation.
