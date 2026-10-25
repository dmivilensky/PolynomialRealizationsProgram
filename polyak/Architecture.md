# polyak: architecture

| Modules | Purpose and article chain |
| --- | --- |
| `Functions`, `Dynamics`, `Interpolation` | Smooth strongly convex objectives, normalization, from-rest trajectories and arbitrary-set interpolation → Definition 2.4, Lemmas A.1–A.3 |
| `Spectral`, `Waves`, `Spiral`, `Growth`, `Energy`, `Duality` | Actual wave measures, feasible spectra, energy bounds and finite certificates → Theorems 2.5–2.6, Appendix A |
| `Boundary`, `Regularity`, `Asymptotics`, `Threshold` | Four spectral families, certified continuation, all-lag signs, endpoint identities, sharp threshold and expansions → Theorems 2.2–2.3, 2.8, Appendix B |
| `Realization`, `FiniteHorizon`, `Results` | One five-dimensional function and start for every horizon, matching dimension-uniform bounds and exact root limits → Theorem 2.1, Appendix C |
| `General` | Arbitrary constant tunings, dominant roots, phase locking, rate and multiplier criteria → Theorems 3.2–3.8, Appendix D |
| `Levels`, `Global` | Full measure program, gap coordinates, periodic approximation, continuous extended threshold and limiting symbols → Theorems 3.10–3.12, Appendix E |
| `Farey` | Lattice positions, Farey parents, first violations, two-atom combs and fan certificates → Theorems 3.15, 3.23, Appendix F |
| `ModeLocking` | Regular periodic data, analytic boundary, uniqueness of the full extremal measure, quantitative locking and exact two-lag points → Theorem 3.16, Appendix G |
| `FareyPlateau`, `GapEdges` | Single-harmonic plateau criterion, uniform large-curvature domain, tip opening, crossings and junctions → Theorems 3.19–3.25, Appendices H–I |
| `CertifiedExamples`, `Numerics`, `Certificates` | Exact rational identities and interval witnesses for the two rational examples, two mixed plateaus and exact 3/13 point; Part I continuation and initialization data → Propositions 3.13–3.14, Theorems 3.17, G.15 |
| `ArticleResults`, `Article`, `Check` | Direct statement-level bridges, all numbered statements in article order, source and transitive axiom audit |

[ArticleMap.md](ArticleMap.md) identifies the precise declarations, PDF numbers
and TeX labels. It also covers the 36 groups of unnumbered mathematics.
The showcase checks actual declarations; its comments explain the translation
between physical spectra and normalized programs. In particular, Part I fixes
one finite-dimensional example for all horizons. General measure realization
uses a common positive constant with a finite-dimensional restriction for each
horizon.

Generated coefficients and boxes are proposals. Their source formulas,
semantic bridges, infinite tails, feasibility and optimality are proved in
maintained Lean modules. The two local data contracts live in
`Certificates/**/Source.json`; converter registration and allowlists belong to
`Tools/Certificates`. The central verification command restores generated
inputs before checking the ordered correspondence and compiling the audit.
Archive digests identify the inputs; the Lean kernel verifies their mathematical use.
