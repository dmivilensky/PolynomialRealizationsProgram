# chebyshev1

[Article and supplementary material](../chebyshev1.pdf).
The library contains realization algebra, sharp drift gains, prefix optimality,
Jacobi block and Green formulas, sine-chain endpoint analysis and energy certificates.
The extensions add local nonlinear confinement and restarts, weighted second-order
errors, reversal laws, exact perturbation formulas, stochastic moments, ratio
algorithms and exact accuracy-dependent drift budgets.

```sh
python3 -m Tools.Verification.Check chebyshev1 --offline --require-complete --jobs 1
```

[Check.lean](Check.lean) is the complete verification file (Lake target `+chebyshev1.Check`).
[Article.lean](Article.lean) checks the reviewed mathematical signatures;
[ArticleMap.md](ArticleMap.md) records their hypotheses and interpretation,
[ArticleAudit.md](ArticleAudit.md) records both manual review passes and the completed repairs, and
[Architecture.md](Architecture.md) explains the proof layers.
Use `import chebyshev1` to import the mathematical library.

`sineEnergy_decimal` proves `1.14269215 < c_sin < 1.14269221` for the actual
elliptic-profile integral; `sineEnergy_rounding` proves rounding to `1.1426922`.
Landen descent, singular endpoint control and quadrature error are proved here.
The generator only proposes integer intervals; kernel reduction checks them.
The finite drift examples have rational certificates: amplification lies in
`(2.24, 2.25)`, `(12.8, 12.9)` and `(704, 705)` for its three drift fractions.
The printed numbers `2.3`, `13` and `700` are illustrative approximations.

Empty Jacobi blocks equal `1`. Operator norms are Euclidean and Hilbert–Schmidt
norms are Frobenius norms. The small-accuracy amplification approximation with
prefactor `1/2` assumes a positive drift fraction; at zero drift amplification is `1`.
The complete trust boundary is in [Trust.md](../Trust.md).

The correspondence inventory follows all 34 numbered statements and 19 groups
of unnumbered mathematics, with 424 signature references. Two manual review
passes and further independent adversarial reviews examined the actual hypotheses, conclusions and proof chains, including
Appendices A–F and the supplementary algorithms. All findings R1–R7 are resolved;
`--require-complete` now passes. Verification reads the hand-reviewed map and Lean
sources; it does not compare manuscripts automatically. Experimental observations,
floating-point performance and open problems are outside proof coverage.

The general realization interface proves translated physical execution from
affine-consistent coefficients, its residual degree and minimax lower bound.
The endpoint mass and universal gain lower bound hold for every final-exact
realization, using a signed profile; positive resolvents, probability coordinates
and Schur upper bounds retain their positive-fibre hypotheses. The operator-norm
time-l2 bound is derived from scalar kernel factorization. Heavy-ball optimality
minimizes the actual worst-curvature root radius over all real constant parameters.

Existing declaration names, types and granular import paths are retained.
`Nonlinear.lipschitzHessian_error_le` remains the segmentwise result with its explicit
trajectory-bound hypothesis. The new `lipschitzHessian_confinement` and
`lipschitzHessian_local_error_le` derive confinement from Hessian hypotheses on a
ball; they do not assume it. Independent-noise formulas state measurability,
integrability, centering and second-moment assumptions explicitly.
Finite-horizon interfaces require random moments and independence only for s<N
on the original probability space. Small-noise statements fix the deterministic
method, horizon, Hessian, initial state and covariance data. The gossip interface
also permits the probability law to vary with p; its uniform remainder bound
preserves the exact p/(1-p) prefactor. Unrescaled weights on the scaled spectral
interval give the same actual trajectory and centered discrepancy.
The graph specialization derives its conditional covariance and state regularity
from fresh independent edge samples. Its isotropic reversal law uses the complete
mean-zero unit sphere, with dimension d-1. General PSD matrix-valued quadratic
conditional covariance requires no common Kraus factorization. Independent matrix
runs derive their filtration from sample independence and need only finite
Hilbert–Schmidt second moments; iid attainment allows full maximizing eigenspace
blocks. Actual variance is averaged over an independent
uniform initial direction, including its nonnegative O(sigma^4) remainder.
Explicit nonlinear translation identifies the physical run about any stationary
point, and transports the actual gradient, Hessian and third tensor. Primitive
data on the original ball construct the centered Hessian control.
The objective expansion is uniform in the full initial vector under pointwise
third differentiability; its sharp second-variation bound follows directly from
local Hessian Lipschitz control.

For an independent replay of all package-owned proofs with the stock Lean kernel:

```sh
python3 -m Tools.Verification.Check chebyshev1 --offline --replay --jobs 1
```

The full replay also rechecks the numerical energy certificates and can take
substantially longer than a cached build.
