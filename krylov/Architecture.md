# krylov: architecture

| Modules | Purpose and article chain |
| --- | --- |
| `LinearAlgebra`, `Secant` | Physical and canonical secants, the latest symmetric model, flag identities and hidden curvature → Section 2, Appendix A |
| `Reference`, `Methods`, `Realization` | Actual CG trajectories, observed algorithms and query histories, quadratic consistency and realization dictionaries → Sections 2–4, Appendices A–C |
| `Variation`, `Envelope`, `Stability` | Exact first variations, adaptive regularity and compact uniform remainders → Section 3, Appendix B |
| `Correction`, `Information` | RFC residuals, sharp second-order minimax bounds, data-indistinguishable scenarios and uniform spectral gates → Section 3, Appendix B |
| `OneGradient`, `Completion`, `Cost` | Missing Jacobi pivot and moment, admissible curvature completions, optimal trials and information-class separation → Section 4, Appendix C |
| `Design` | Christoffel objectives, all-measure optimal designs, finite support and Chebyshev comparisons → Section 5, Appendix D |
| `Strings`, `LotkaVolterra`, `ContinuumControl`, `ContinuumBV`, `Asymptotics` | Stieltjes strings, optimal feedback and uniqueness, discrete recovery, sharp spectral limits and measure tails → Section 5, Appendix D |
| `Numerics`, `Certificates` | Exact rational barriers, separating-orbit brackets and certified numerical constants → Proposition D.14 |
| `Tensor`, `Functions`, `Nonlinear`, `Convergence` | Genuine scalar objectives, compatible third derivatives, cubic witnesses, secant recurrences and SS1/SS1-F orders → Section 6, Appendix E |
| `XR` | Window selection, numerical-policy mathematical models, actual safeguarded executions, globalization and conditional growth to full memory → Section 7, Appendix F |
| `Article`, `Check` | Statements in PDF order, mathematical correspondence, full import closure and axiom audit |

Operator scenarios and genuine function realizations are distinct layers.
Canonical norms are congruence invariant; the source dictionaries transport
the physical steps and observations into those norms before estimates are
applied. Local rates retain convergence, independence and trial-adequacy
hypotheses. Global stationarity uses safeguarded descent and Armijo acceptance.

[ArticleMap.md](ArticleMap.md) identifies the terminal declarations and the
bridges needed for each printed claim. Its unnumbered groups cover the
algorithm listings, accounting conventions, intermediate formulas and
certified constants. Experimental measurements use a separate implementation
and reproduction pipeline in `krylov-code`.
