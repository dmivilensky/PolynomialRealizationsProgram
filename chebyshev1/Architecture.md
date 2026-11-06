# chebyshev1: architecture

| Modules | Purpose |
| --- | --- |
| `Algebra`, `Realization`, `Spectral` | Ordered products, insertion expansions, spectral kernels, affine-consistent physical execution, residual minimax, signed universal endpoint profiles, operator time-l2 bounds, resolvents and sharpness |
| `Chebyshev`, `Stepsize`, `Prefix`, `TwoTerm` | Normalization, exact recurrences, uniqueness, sharp gains and finite stepsize/prefix separation |
| `Jacobi` | Finite-horizon converse classification, block determinants, insertion orders, drift bounds, Green profiles, inverse spectral laws and reversal |
| `Background` | Chebyshev minimax, finite Favard construction and uniqueness, recorded CG and actual replay, Schur majorization, global heavy-ball optimality and parameter limits, graph spectrum and certified rounded comparisons |
| `Jacobi`, `Prefix`, `SineJacobi`: ratio algorithms | Positive continued-fraction denominators and equality of actual executions with the existing methods |
| `SineJacobi`: finite chain | Rogers/Fourier formulas, spectrum, sine weights and all-block endpoint maxima |
| `SineJacobi`: endpoint analysis; `Analysis` | Mesh estimates, elliptic profile, singular ODE, Lp convergence and the first Green diagonal's logarithmic expansion |
| `SineJacobi`: energy certificates; `Numerics` | Landen descent, graded quadrature and kernel-checked rational witnesses |
| `Nonlinear` | Segment FTC, confinement, restarts, weighted second variation, scalar cubic sharpness and monotone prefix scaling profile and explicit physical translation about arbitrary stationary points |
| `Perturbations` | Exact forced recurrences, full-vector Taylor expansion under pointwise third differentiability, actual objective tensors and radial norm derivatives |
| `Stochastic` | General PSD quadratic conditional covariance, actual finite-horizon independent-matrix/gossip runs on the original probability space, spherical moments, eigenspace-block iid attainment, varying-law gossip remainder, pathwise rescaling and mean-zero reversal |
| Drift/accuracy modules in `Chebyshev` | Exact drift budgets, least integer accuracy horizons, condition-number and small-accuracy limits |
| `Article`, `Check` | Reviewed signature inventory; complete import and axiom checks |

Products act in causal order, with the first step on the right. Memory and physical
coordinates use arbitrary finite types. Spectral hypotheses enter estimates;
algebraic identities also hold without them. The manually reviewed article map
follows the 34 numbered main/supplementary statements and records exact hypotheses
and conclusions. All 34 numbered statements and 19 prose groups have undergone
two manual review passes; [ArticleAudit.md](ArticleAudit.md) records the completed
repairs and validation. A related signature alone does not establish correspondence.

The original modules and their public signatures remain available. Extensions
live in additional modules and use the existing realizations; downstream
packages can continue to import the same granular paths. The public root imports
the complete mathematical library, while `Check` also imports the reviewed
showcase and runs the module-owned declaration/axiom audit.
