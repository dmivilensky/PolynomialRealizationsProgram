# bezout

Lean formalization of the mathematical results in
[Chebyshev-Exact Acceleration under Gradient Variation](../bezout.pdf).

The package covers Theorems 2.1, 3.1 and 4.1, Lemmas C.1 and C.2,
Proposition D.1, both physical algorithms, and the supporting unnumbered
mathematics. [Article.lean](Article.lean) checks the article-facing signatures;
[ArticleMap.md](ArticleMap.md) records hypotheses, normalizations, execution
semantics and the correspondence for the additional claims.

The unrestricted causal-history classification retains arbitrary real signs
and arbitrary memory. Flat attains both exact additive optima; Balanced
attains all spectral, operator, Hilbert–Schmidt and actual-query local relative
optima, including the odd-horizon correction. Both arbitrary and symmetric
matrix perturbations are covered. Risks are defined by actual physical
executions and probability models, with literal supremum and positive-scale
limsup dictionaries. The martingale upper bounds require conditional
centering and second moments, with no independence assumption.

Algorithms 1 and 2 execute in four and six vector registers with exactly N
oracle calls. Their actual queries and outputs agree with the constructed
histories for every time-dependent oracle. Cached scalar preparation has
proved linear arithmetic work and storage, and every division is valid at
its actual execution prefix. The exact classical variance and its positive
fixed-interval limit, the Flat asymptotic variance and even-horizon
incompatibility of the two optima are also proved.

The comparison layer implements Prefix, root-step LF, sine–Jacobi, averaged
DFB and M-ASG, including extrapolated queries, momentum resets and incomplete
final stages. Their own exact terminals and physical responses feed the
finite predictions. General covariance traces, sharp fixed-Hessian additive
gains, actual signal matrices and endpoint-mass transfer bounds are included.
The full finite-sign oracle output has an exact multilinear expansion;
its mean is the nominal output and its variance is the squared first
variation plus a nonnegative remainder of order delta to the fourth.
Root ordering preserves both first-variation norms and the finite-noise
terminal distribution. Exact product variances and both dyadic LF/Prefix
asymptotics retain the finite interior spectral modes.

The experimental sections' general models are formalized with symbolic
parameters: ridge gradients and the average minimizer, actual subtractive
rounding with fresh adaptive inputs and worker averaging, and the coupled
network projector, cycle spectrum and isometric active-subspace execution.
A single temporal dither tape gives the full quantized oracle trajectory, its
proved martingale errors and exact MSE with the method's own terminal bias.
Concrete experiment configurations, decimal approximations, measured results,
plots, Monte Carlo/bootstrap calculations and bibliographic history are
excluded. Exact rational constants and symbolic horizon formulas are retained.

```sh
python3 -m Tools.Verification.Check bezout --offline --require-complete --jobs 2 --replay
```

Use `import bezout` for the mathematical library. Modules are organized as follows:

- `History/`, `Polynomial/`, `Synthesis/`: physical oracle semantics, Bezoutian
  identities, degree orders and constructive unique history reconstruction.
- `Lower/`: signed mass certificates and sharp physical four-corner bounds.
- `Probability/`, `Risk/`: genuine martingales, covariance, dither, actual risks
  and their attained minimax values.
- `Flat/`, `Balanced/`: explicit constructions, positive factors and exact gains.
- `Analysis/`, `Gains/`: functional calculus, actual matrix derivatives,
  symmetric witnesses and uniform relative-error remainders.
- `Algorithms/`: physical register programs and counted scalar preparation.
- `Comparisons/`: actual competitors, classical variance and finite-spectrum asymptotics.
- `Channel/`: literal signal matrices, finite-noise expansions and root ordering.
- `Models/`: symbolic ridge and coupled-network models with physical transport.
- `Properties/`: polynomial minimax, incompatibility and analytic limits.

Only granular analytic dependencies are imported from `chebyshev1` and mathlib;
no numerical proof archives or experiment generators are required. Direct
supporting quadratics replace the auxiliary constrained-optimizer proof,
and positive parity tails replace the auxiliary parity matrix factorization.
The physical query recurrences and register algorithms are verified directly.

[Check.lean](Check.lean) requires complete source import coverage and audits
every owned declaration. The only permitted transitive axioms are `propext`,
`Classical.choice` and `Quot.sound`; there are no unsafe-helper exceptions.
The package is registered in Lake and the shared
[verification entry point](../Tools/Verification/All.lean).
[Trust.md](../Trust.md) describes the common proof trust model.
