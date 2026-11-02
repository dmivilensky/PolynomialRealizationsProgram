# MS-L-BFGS implementation

The C solver implements the published uniform polar-kernel method with
L=M=8. The Python solver provides an independent numerical reference.

## Primary source

F. V. Gubarev, *A Multi-Secant Limited-Memory BFGS Method*, Optimization
Online, 7 March 2026:
[landing page](https://optimization-online.org/2026/03/a-multi-secant-limited-memory-bfgs-method/),
[paper](https://optimization-online.org/wp-content/uploads/2026/03/ms-lbfgs.pdf).
The publication supplies the algorithm and its experimental configuration.

## Algorithm correspondence

| Published component | C implementation |
|---|---|
| Uniform inverse block update (9), polar kernel | SVD of the nonsymmetric overlap; inverse square-root factor from left singular vectors |
| Largest admissible recent window (18)–(19) | `select_window`, logarithmic determinant and positive square-root model Grams |
| Symmetric damping (20)–(21) | `cn_ms_damping`, then simultaneous changes of the newest coordinate and gradient pair |
| Whole-update memory cuts, Figure 1 | newest L pairs; longest suffix of complete block updates contained in those pairs |
| Compact inverse representation (44) | factored projector products and positive update factors; independent dense recursion tests |
| Scalar initialization, Section 4.4 | gamma = sum(singular values of overlap) / squared Frobenius norm of window Y |
| Search policy, Section 5 | initial/reset Goldstein steepest descent; otherwise unit trial and guarded quadratic Armijo |
| Failed search reset | discard model once, retry Goldstein steepest descent; terminate if that search fails |
| Nonfinite function responses | shrink the step before requesting a gradient |

The gamma formula uses the exact identity
`||r^(-1) O||_F^2 = trace(K_R) = sum(sigma_i)`, with `r r^T = K_R`.
The inverse-kernel factor is `diag(sigma_i^(-1/2)) U^T`, so its squared
product is exactly `K_R^(-1)`. These choices avoid a formed inverse Gram
matrix and do not alter the polar update.

Uniform windows M = 1, 2, 4 are supported for existing sensitivity
configurations. The native optimizer rejects the unused positive single-pair
variant M = 0 and the unused exact-newest variant explicitly. The internal
M = 0 model helper remains available only for algebra diagnostics.

The angular damping solver can miss a narrow
box corner when given almost antiparallel data with negative signed overlap.
Production uniform variants use the absolute overlap in damping, so that case
is outside their domain. It is not a supported positive-curvature optimizer.

## Explicit implementation choices

The paper specifies the search structure but leaves the scalar interpolation
constants open. The search constants are: Armijo constant
1e-4, initial trial 1, quadratic contractions guarded between 0.1 and 0.5;
Goldstein constant 0.25, initial step 1/||g||, expansion factors between 2
and 10, bracket bisection, and at most 100 trials. Goldstein can return the
best sufficiently decreasing point if its two-sided test exhausts the trial
limit. The independent reference uses the same constants.

Damping minimizes the same two-dimensional constrained objective as the
paper. Our numerical solution uses exact quadratic boundary roots on rays,
91 angular samples and 40 golden-section refinement iterations, rather
than the activity-pattern Newton solver described by the author. Constraints
are scaled homogeneously before solution. Feasibility and objective values
are checked against an independent grid and the reference solver. No
curvature floor or sign replacement is inserted into the uniform variant.

For Hessian products needed by the window tests, the inverse compact model
is inverted on the thin QR span of [S,Y]. A second QR factors its positive
features. This preserves the same matrix without squaring its condition
through normal equations; no QR column is discarded, no ridge is added,
and no eigenvalue is clipped. All large and small work arrays are allocated
once at optimizer creation and reused. SVD/QR failures terminate as numerical
failure or skip an undefined candidate pair, with no alternative Hessian
silently substituted.

Campaign stopping uses the common Euclidean gradient target, budgets and
oracle accounting for all methods. The paper's infinity-norm stopping test
is not used in the common benchmark. Trial points request function values;
gradients are requested at accepted points. Existing oracle exceptions,
including convergence and budget exhaustion, propagate unchanged.

## Validation

`tests/test_mslbfgs_native.py` directly calls the same C model and optimizer
through the diagnostic ABI and the same SciPy BLAS/LAPACK capsules. It checks:

- retained windows, stored pairs, damping count and scalar initialization
  against the independent Python reference across repeated memory cuts;
- inverse products against literal dense block recursions using independently
  reconstructed polar kernels, plus `B H = I`;
- sizes below and above the memory limit, window lengths 0, 1, 3 and 8;
- damping feasibility and objective against a 151-by-151 independent grid;
- negative curvature in the uniform and positive-damping variants;
- zero-pair skipping and preservation of callback exceptions;
- full C optimization on a rotated conditioned quadratic and Rosenbrock,
  including agreement of the first eight gradient-query locations.

Native compilation uses optimization, strict floating-point behavior and
`-Wall -Wextra -Werror`, with the same numerical capsule ABI as XR.

## Damping and sensitive trajectories

An additional 1,200 physically admissible damping inputs spanning p/q from
1e-18 to 1e18 were checked against multi-start SLSQP with analytic constraint
Jacobians: maximum positive objective discrepancy was 7e-15. A further 3,000
inputs across p/q from 1e-30 to 1e30 were compared with 8,193 angular samples
and independent polynomial coefficients plus scalar refinement; no objective
gap above 1e-9 was found. Common rescaling by factors from 1e-250 through
1e250 preserved the solution to working precision. These checks supplement
the diagnostic tests; they are not formal floating-point certification.

FLETBV3M at n=1000 is a sensitive nonconvex example: the native and reference
optimizers enter different basins after tiny initial rounding differences.
Replaying the same 114 accepted reference secants through the C model gave
identical window choices throughout, with maximum relative product errors
1.73e-14 for H times the gradient and 2.13e-14 for B times the gradient. The
native search ultimately stops above the common gradient target; this result
is retained as a failure, without a problem-specific search modification.
