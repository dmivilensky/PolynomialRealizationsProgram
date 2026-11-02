# Competitor implementations

Every method uses the common observation interface, gradient target and
resource limits. Numerical stops and search failures retain their status.
The registry in `src/xrbench/resources/methods.json` selects the implementations.

| Method | Implementation | Primary parameters |
|---|---|---|
| L-BFGS | SciPy compiled core with Python reverse communication | 20 pairs, 20 search trials |
| L-CG_DESCENT | Author C implementation through pycgdescent | 11 directions |
| MS-L-BFGS | Independent C implementation | Uniform L8M8 |
| SC-MSS | Independent C implementation of SC-INF-D | Three model pairs, five preceding curvatures |
| SC-SR1 | Independent C implementation of SC-INF / Init. 2 | Five pairs, seven preceding curvatures |
| O-ACCEL-B | Independent C implementation | History 20, displacement cap `1e-4`, regularization `1e-12` |

The C implementations share strict compiler settings, preallocated workspaces
and the SciPy LP64 BLAS/LAPACK interface with XR. The Python implementations
provide independent algebra and trajectory references. The rationale for each
primary parameter is in [PresetRationale.md](PresetRationale.md).

## L-BFGS

The unconstrained SciPy solver retains its scalar initialization, curvature
filter, memory truncation and More–Thuente search. Native `ftol=gtol=0`
delegates the requested target to the common oracle while preserving native
stagnation stops. Every function/gradient request is counted.

Sources: [author software](https://users.iems.northwestern.edu/~nocedal/lbfgsb.html),
[Algorithm 778](https://doi.org/10.1145/279232.279236),
[Morales–Nocedal remark](https://doi.org/10.1145/2049662.2049669), and
[SciPy's interface](https://docs.scipy.org/doc/scipy/reference/optimize.minimize-lbfgsb.html).

## L-CG_DESCENT

The author controller retains its search, approximate-Wolfe switch, quadratic
trials, subspace corrections and restart rules. `StopFac=0` and a small native
gradient tolerance delegate success to the common target. The author's
small-dimension L-BFGS branch is retained. A caller-owned work array permits
callback exceptions to unwind without leaking native storage.

Sources: [author archive](https://www.math.lsu.edu/~hozhang/software-archive.html),
[Hager–Zhang paper](https://doi.org/10.1137/120898097), and
[pycgdescent adapter](https://github.com/alexfikl/pycgdescent).

## MS-L-BFGS

The uniform polar-kernel update, adaptive suffix, symmetric damping,
whole-block memory cuts and scalar initialization follow Gubarev's
[published method](https://optimization-online.org/2026/03/a-multi-secant-limited-memory-bfgs-method/).
Initial/reset Goldstein and subsequent guarded Armijo searches use the
explicit constants in [NativeMSLBFGSAudit.md](NativeMSLBFGSAudit.md).
That document specifies the two-dimensional damping solve, compact factors,
failure policies and independent dense comparisons.

## SC-MSS and SC-SR1

The compact matrices, separable shape-changing infinity subproblem and
trust-radius controller follow the papers and author software. Both use
More–Thuente initial search `(c1,c2)=(1e-4,0.9)`, maximum step five and up to
3000 trials. A finite sufficient-decrease point can seed the model at a
search boundary. MSS dense complement initialization starts at one and takes
the latest positive curvature quotient. SR1 uses the updated history maximum
in its physical compact storage gate.

Sources: [MSS paper](https://doi.org/10.1080/10556788.2023.2296441),
[SCMSS software](https://github.com/johannesbrust/SCMSS),
[SC-SR1 Algorithm 1030](https://doi.org/10.1145/3550269),
[ACM software](https://calgo.acm.org/1030.zip), and
[SR1 subproblem analysis](https://doi.org/10.1007/s10589-016-9868-3).
[NativeSCAudit.md](NativeSCAudit.md) details pair selection, the first-pair gate,
subproblem hard cases and numerical differences from the MATLAB routines.

## O-ACCEL-B

Preconditioner B, objective-based acceleration, descent checks, cyclic history,
More–Thuente search and restart follow
[Riseth](https://doi.org/10.1002/nla.2216) and the
[author software](https://github.com/anriseth/objective_accel_code).
[NativeOAccelAudit.md](NativeOAccelAudit.md) gives the coefficient system,
regularization, cached products, search limits and numerical fallback.

## Mathematical correspondence and tests

The Lean library proves exact-real update and model identities under their
hypotheses. Native controllers, searches, rank decisions and floating-point
arithmetic are checked independently by tests. In particular, the Hager–Zhang
coefficient theorem concerns its scalar update; the author limited-memory
controller adds subspace and search mechanisms. The L-BFGS inverse recursion
is compared with an independent dense map and actual SciPy directions.

The native tests reconstruct dense MSS/SR1 and block-BFGS matrices, solve
independent scalar/ball subproblems including negative-curvature hard cases,
compare evaluated trajectories, check memory truncation and pair rescaling,
and verify oracle budgets and exception propagation.
