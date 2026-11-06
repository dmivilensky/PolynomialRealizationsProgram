# nesterov: architecture

The package follows the article dependency graph, with the public import,
ordered showcase, source correspondence and shared audit used by the other
article packages.

| Modules | Role and article obligations |
| --- | --- |
| `Stationary` | Arbitrary finite memory, coefficient polynomials, actual queries/execution, centering, uniqueness, state growth and exact finite-prefix realization. Definition 4.3 and Appendix A. |
| `Rates` | Literal all-Hilbert supremum before the horizon limit, restart closure, submultiplicativity, positive eigenmode lower bounds, root limit and infimum. Definition 2.2 and Lemma 2.3. |
| `Momentum` | Actual previous/current execution, stationary specialization, τ=0 Polyak bridge, gradient-correction/QHM/HNAG dictionaries, initialization and rate transport. eq:M and Remark 4.4. |
| `Quadratic` | Literal roots and attained root-radius maximum, scalar Jury criterion allowing either determinant sign, exact stability threshold, price and unique Polyak equality. Lemma 2.1 and Theorem 2.7. |
| `Smooth` | Actual convolution and averaged gradient, unchanged μ,L, C∞ approximation with recentered minimizer, finite-execution convergence and exact finite-horizon supremum density. Remark 2.4. |
| `Spectral` | Division-free amplitudes u,p; exact planar and L² slacks; arbitrary-set interpolation; compact feasible measures; genuine all-time stationary realizations; orthogonal state rotation; literal atomic real coordinates. Theorem 4.7(d). |
| `Duality` | Finite strict alternative for the common value variable, finite support certificates and uniform persistence under simultaneous g, skew and exponent perturbations. |
| `IQC` | Source Hermitian multiplier, real Fourier/Parseval graph, general causal feedback continuation, stable companion and Green response, dimension-independent all-Hilbert energy estimates and the one-exponent principle. |
| `IQC/KYP` | Proved strict quadratic storage via half-line coercivity and Hilbert quadratic maximization; scalar matrix chosen before the Hilbert space, tensor transfer, telescoping finite value correction, literal original momentum state and uniform from-rest Lyapunov estimate. Proposition C.15. |
| `Closure` | Actual spectral maximum, exact equality of the uniform rate and exp T, certificate thresholds and the complete interval above the middle quadratic radius. Theorem 4.7(a–c). |
| `Attainment` | Normalized compactified lag families, analytic limiting dual probability, a common finite carrier for every optimizer, strict minimizer slack, finite active lags and half-degree atom count; literal real quadratic/nonquadratic attainment. Theorem 4.7(e). |
| `Realization` | One scalar curvature avoids every noninitial return; product interpolation repairs the entire initial datum; one objective and one actual from-rest start work for all horizons. Real dimension 2J+1, vanishing auxiliary coordinate and exact rest/free factor equalities. Corollary 4.8. |
| `Phase` | Endpoint characteristic factorization, principal polar phase including ω=π, all three lag-one/mixed tests, exact rational one-atom criterion, actual periodic ℝ³ startup/divergence, separation of quadratic modes and the Hill recursion. |
| `Flow` | Full bounded-set-Lipschitz potential class, minimizer and global ODE well-posedness in arbitrary Hilbert space, exact Lyapunov derivative, spread spiral interpolation and smooth extension, literal real witnesses, exact state/value/energy infima, optimal damping and single-spiral obstruction. |
| `Slow`, `Faithful`, `Trace` | Fixed-memory families; root/quotient Cᵏ regularity derived from coefficient regularity; uniform slow normal form and two roots with multiplicity; exact query-normalized all-lag sampling and forced charge; actual-rate ceilings and real orthogonal witnesses; faithful discretization, fast resonance and half-step obstruction; rational transfer expansion, trace identity, endpoint cancellation and TMM transfer rigidity. |
| `TwoStep`, `FiniteCondition` | Exact cubic/mixed polynomials and compact-uniform coefficient expansions; quadratic and full/rest bulk/boundary constants, including the stable zero-constant edge; instability wall and exact period bands/counts; alternating mode; exact finite NAG optimum and all-family frontiers; known physical tunings, initialized QHM and the sharp HNAG++ corner rate; sharp finite-condition thresholds, negative-frequency localization, lag-two multiplier, comparison and open convergence interval. |
| `Spread` | Smooth normalized convolution kernel, quantitative Fourier gap, actual band measure and density, reciprocal reweighting, exact extreme-charge slacks, strict margins for every integer lag and finite atomic approximation on the original band. Lemma C.17. |
| `Layer` | Exact boundary-layer constants, compact-uniform cubic/mixed symbols, positive certificates, rational periodic divergence, all-lag spread witnesses and actual initialized rate bounds; matched full/rest limits, condition-number scales, one-atom obstruction and all-family acceleration criterion. Theorem 6.5. |
| `Robust` | Literal finite-condition design interval, exact characteristic factorizations and circle symbol, strict larger-circle certificate, exact full/rest/quadratic rates, arbitrary-L normalization, TMM deficit remainder, GD endpoint execution, reported-output rate and balance curve. |
| `Corner` | Attained continuous/discrete lag-one minima, exact compact-uniform coefficient and endpoint expansions, alternating and fixed-band spread witnesses, actual strict rate bounds and condition-number bounds, all matching criteria, optimal wedge, physical arc and exact arithmetic gap; literal limiting half-step measure cone, exact rational atom classification and gap-supported spectral obstruction. |
| `Optimal` | General near-corner expansion with no bounded scaled coordinates; necessity through alternating, bounded/moderate spread and deep periodic obstructions; arbitrary stable physical-family iff, equivalent liminf/ratio criterion, literal κ statements and beyond-corner consequence. |
| `Oracle` | Unrestricted adaptive deterministic value-and-gradient queries with horizon/dimension-dependent policies; proved smooth strongly convex simplex extension, geometric zero chain, adaptive resisting frame, genuine finite hard instances, literal supremum before root limsup, arbitrary μ,L policy normalization and TMM attainment. External-optimality clause of Corollary 7.1. |
| `Article`, `Check` | Proved signatures in article order; every source and every owned declaration audited. The semantic review records every numbered statement, labelled formula and supporting obligation. |

The function classes are the existing `polyak.SmoothStronglyConvex` and
`polyak.CenteredSmoothStronglyConvex` predicates on genuine gradients. The
stationary rate is defined independently from Polyak's original from-rest rate;
the two coordinate and initialization conventions are connected by proved bridges.

General stationary methods impose only the article's consistency and explicitness
conditions. Stability, nonnegative momentum/extrapolation, coprimality and smooth
parameter-family assumptions enter only the statements that require them.
The generic stationary model permits common roots and unstable methods.

The Fourier argument uses the finite-lag symbol directly before constructing the
stable causal feedback plant. It never divides by the query amplitude u, so
query zeros and shared characteristic modes remain covered. The storage argument
is a proof in Lean, rather than an assumed KYP matrix or a numerical certificate.

The boundary proof separates nonquadratic T≠0 attainment from the quadratic
boundary. Its common carrier is selected before the optimal measure being bounded;
the largest active lag may come from any one fixed optimizer. The startup repair
then selects its function and initial state before every execution horizon.

Slow families are endpoint germs on ε≥0. Coefficientwise continuity is the
baseline assumption; higher regularity is stated separately and inherited by
the distinguished root through a proved finite-dimensional implicit-function
bridge. No extension of the given coefficients to negative ε is assumed.
General-family wall, frontier and Nesterov optimality statements do not assume
convergent tuning parameters. Compact subsequences and exactly matching real
extensions are constructed inside their proofs. Extended-real coefficients
retain unstable family members in the rate ceilings.

The continuous class assumes only gradient Lipschitz continuity on bounded sets.
Global continuation uses mechanical energy and uniform local existence times,
without compactness of Hilbert balls. Spread witnesses are finite from the outset:
the frequency scale is selected before the common quadrature grid, and the
short/compact/long lag bounds cover every positive real lag.

The discrete spread construction fixes the existing normalized Polyak bump ψ
once and for all, then uses its convolution with itself. Smoothness, support,
nonnegativity, unit mass, Fourier decay and the quantitative Fourier gap are
proved for this concrete kernel. This implements the source's permitted fixed
bump choice; it does not assert the same quantitative constants for every
arbitrary bump. Reciprocal reweighting and exact extreme-charge identities give
strict margins for every integer lag. A uniform inactive tail and finite
quadrature then produce atoms on the original band with strict minimizer slack.

The layer proof fixes the bandwidth and margin constants before ε. The rational
period and finite spectrum may depend on ε; the resulting objective, initial
state and positive prefactor are selected before all execution horizons. Actual
band maxima are attained by compactness, so the literal source maximum and
little-o hypotheses also imply the general envelope-based spread theorem.
The undivided rescaled symbol H/(ε√ε) converges uniformly on compact φ sets,
including φ=0; the divided symbol H/(εξ) is asserted uniformly only on positive
compact φ sets. The proofs require only the stated coefficient limits of the
scaling family. Exact κ powers and rational-period limits connect these symbols
to the κ−1/4 layer width and κ−1/8 frequencies, while the acceleration criterion
also covers oscillating or unbounded scaled deficits. The corner construction
uses fixed frequency bands, while the unrestricted optimality proof also controls
shrinking bands and deep dips through actual periodic trajectories.


The oracle lower bound concerns arbitrary deterministic first-order policies;
queries and outputs may be nonlinear, discontinuous and depend on all earlier
points, function values and gradient vectors. There is no linear-span restriction.
The objective and dimension may depend on the finite horizon, as allowed by the
uniform supremum taken before the root limsup. The resisting-frame construction
makes the complete transcript consistent with one genuine smooth strongly convex
function. The arbitrary-μ,L bridge rescales both values and gradients in the
transcript and proves the policy execution identity. TMM is embedded as an actual
one-call-per-update policy, and its uniform rate bounds the oracle envelope.
