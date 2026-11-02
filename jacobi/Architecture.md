# jacobi: architecture

| Modules | Purpose and article chain |
| --- | --- |
| `Finite`, `Packing` | Entire polynomial fibres, positive-weight reconstruction, reversal, criticality, Gram–Cholesky and exact finite packing → §1 and Theorem D.4 |
| `Continuum`, `Rearrangement`, `Variational` | Genuine integral operators, spectral moments, rearrangement, compactness, variations, constraint qualification and all-candidate Transfer → Appendix D |
| `Young`, `Elliptic`, `Keller`, `Fredholm`, `RootMass` | Sharp inequalities, complete optimizer problems and attaining calibration formulas → lower bounds and Theorem 4.1 |
| `Bessel`, `Jacobi`, `Hankel`, `Oscillation`, `Reference` | Original special functions, numbered zeros, uniform edge estimates, reference basis and characteristic normalization → Appendices A–C and E |
| `GelfandLevitan` | Actual GL inverse, regularity, transformed bases, midpoint conditions and full spectral operator, compact-test action and full-domain weak action → canonical continuum limit |
| `Support`, `Comparison` | Concrete support chain, finite waves, weight ratios, uniform Gram–Cholesky and eigenvector/resolvent limits → Theorem 2.1 |
| `Analytic` | Common complex-order disks, analytic GL, actual profile energy, contact at U and shifted resolvents → Theorems 4.2 and C.5 and Appendix E |
| `Trichotomy`, `Counterexample`, `Applications` | Local unit-source Green regularity, normalized positive factors, exact exponential kernel, transported eigenframe and trace-complete packed spectrum; endpoint geometry, fibre-energy limits and actual method gains → Green coordinate and applications |
| `Finite.Closed*`, `Variational.Closed*`, `Applications.AllThreeTerm`, `Applications.NesterovSharp` | Closed fibres, attained minima, the quarter-spectrum transfer and sharp symmetric endpoint constant in both parities → Lemma 5.2 and Theorem 5.3 |
| `Jacobi.Standard*`, `Finite.StandardGreen`, `Finite.Flow*`, `Finite.Resolvent*`, `Applications.Standard*`, `Applications.NesterovComparisons` | The standard Gauss realization, conductance Green kernel, global resolvent flow, exact descent constants, sorting and optimal endpoint ratios → Theorem 5.4, Proposition 5.5, Theorem 5.6 and Corollary 5.7 |
| `Article`, `Check` | Ordered source showcase, complete import coverage and declaration/axiom audit |

Operators and densities are shared with the earlier articles. New special
functions and realizations are connected to those interfaces by explicit
identification theorems. The library root imports mathematics; Article imports
the root, and Check imports Article. This keeps the verification entry point
outside the proof dependency graph. Each Lean object documents its source,
downstream use and mathematical proof idea. Auxiliary proof replacements and excluded decimal illustrations are explicit
in the source correspondence; no such item is an axiom or theorem premise.
