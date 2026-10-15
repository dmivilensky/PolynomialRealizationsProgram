# 2606.16671v2: architecture

| Modules | Purpose and article chain |
| --- | --- |
| `Algebra`, `Realization`, `Spectral` | Ordered products, variation kernels, Euclidean/Frobenius bounds and attainment → Lemma 1.1, Proposition 1.3 |
| `Chebyshev`, `Stepsize`, `Prefix`, `TwoTerm` | Normalization, explicit recurrence, uniqueness and sharp prefix lower bounds → Theorems 1.4–3.1 |
| `Jacobi` | Block determinants, all insertion orders and finite/cosh bounds → Theorems 4.1–4.3, Corollary 4.4 |
| `SineJacobi`: finite chain | Rogers/Fourier formulas, spectrum, weights, block maxima → Appendix E, Algorithm 2 |
| `SineJacobi`: endpoint analysis; `Analysis` | Uniform mesh bounds, actual elliptic profile, singular ODE and dominated Lp convergence → Theorems E.3–E.4, 5.1–5.2 |
| `SineJacobi`: energy certificates; `Numerics` | Landen transformation, graded quadrature and kernel-checked rational witnesses → Theorem 5.2's energy value |
| `Nonlinear`; drift/accuracy modules in `Chebyshev` | Segment FTC, Lipschitz Hessians and attained drift scales → Corollary 5.4, Remark 5.5 |
| `Article`, `Check` | Ordered paper statements; complete import and axiom checks |

Products act in causal order, with the first step on the right. Memory and physical
coordinates use arbitrary finite types. Spectral hypotheses enter estimates;
algebraic identities also hold without them. Each source header names its
article target and a concrete downstream Lean use.
