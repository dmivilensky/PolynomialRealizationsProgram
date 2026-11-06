# nesterov

Lean formalization of
[Exact (Non-)Accelerations of Heavy-Ball Discretizations](../nesterov.tex).
The library covers all 88 numbered results, definitions and remarks,
53 labelled formulas and 23 groups of supporting mathematical assertions.

Use `import nesterov` for the mathematical library.
[Article.lean](Article.lean) presents 654 checked signatures in article order;
[ArticleMap.md](ArticleMap.md) records their source correspondence.
[Architecture.md](Architecture.md) describes the proof dependencies.

The proofs cover stationary methods and actual uniform/rest rates, quadratic
stability, spectral closure and attainment, IQC/KYP certificates, continuous
heavy-ball flow, fixed-memory ceilings and faithful discretization, exact
two-step and boundary-layer rates, robust momentum/TMM, corner bounds and the
characterization of optimal tuning families. The HNAG dictionary identifies
HNAG+ with TMM and gives the sharp full-class HNAG++ coefficient `2√2/3`. The deterministic first-order
oracle lower bound and TMM attainment hold for arbitrary `0 < μ < L`.
Granular Polyak imports supply the existing function classes, interpolation
and supporting analytic facts; the dependency remains one-way.

## Lyapunov proofs

The discrete-time construction for Proposition C.15 lives in
[IQC/KYP/StrictStorage.lean](IQC/KYP/StrictStorage.lean), with certificate data
in [IQC/KYP/Data.lean](IQC/KYP/Data.lean) and the original-objective comparison,
strict dissipation and iterate bounds in
[IQC/KYP/SourceOriginal.lean](IQC/KYP/SourceOriginal.lean).
The continuous-flow identity and decay bounds live in
[Flow/Lyapunov.lean](Flow/Lyapunov.lean).

## Verification

From the repository root:

```sh
python3 -B -m Tools.Verification.Check nesterov --offline --require-complete --replay
python3 -B -m Tools.Verification.Check all --offline
```

[Check.lean](Check.lean) audits every owned declaration, including private and
generated declarations, and verifies complete source import coverage.
The only permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. There are no unsafe-helper exceptions or numerical proof archives.

The public library contains 510 mathematical modules. The full audit checks
512 source files and 7376 owned declarations; independent stock-kernel replay
checks all 513 modules.
