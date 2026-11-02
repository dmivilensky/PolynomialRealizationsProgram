# O-ACCEL-B implementation

## Sources

- A. N. Riseth, *Objective acceleration for unconstrained optimization*, Numerical Linear Algebra with Applications 26(1), e2216 (2019), DOI [10.1002/nla.2216](https://doi.org/10.1002/nla.2216), [author manuscript](https://arxiv.org/abs/1710.05200): Algorithm 1, equations (3), (10), (21), (30), Sections 3.2 and 3.5.
- [Author MATLAB source `ngmres_o.m`](https://github.com/anriseth/objective_accel_code/blob/701f7a5e43ef3549ab7650a3dd89b6bb8642abfd/ngmres_o.m): lines 95–141 (window, cached coefficient system, regularization), 153–187 (candidate/descent/search), 209–223 (cyclic history/cache update). This is an equation-based C implementation, not redistributed MATLAB code.
- SciPy `optimize/_dcsrch.py` (installed version recorded in native build metadata), the maintained MINPACK-2 DCSRCH/DCSTEP translation: [upstream source](https://github.com/scipy/scipy/blob/main/scipy/optimize/_dcsrch.py). The C translation retains its two stages and four safeguarded interpolation cases. Its BSD-3-Clause notice is distributed in `src/xrbench/native/COMPETITOR_LICENSE.txt`.

## Controller correspondence

The primary native preset is O-ACCEL with preconditioner B, maximum window 20, displacement cap `delta=1e-4`, and shift parameter `eps0=1e-12`. Preconditioner B advances by `-min(delta,||g||)g/||g||`. The coefficient system is `(D' E + eps I) alpha = -D' gP`, with `D_i=x_i-xP`, `E_i=g_i-gP`; `eps=eps0*max(max diag(D'E),eps0)`. The acceleration is `s=D alpha`. A non-descent candidate resets the window at the preconditioner point. Otherwise More–Thuente starts at one with c1=1e-4, c2=.1, maxfev=20, xtol=1e-8, and step bounds 1e-16 to 65536. Window replacement is cyclic and restarts keep exactly the current accepted point.

Numerical failure of the coefficient solve or nonfinite coefficients discards acceleration and restarts. A search warning may retain the best Armijo trial; absence of any such point discards acceleration. These guards follow the independent Python/Optim-style reference used by this project. They are documented guards, rather than claims of bitwise equality to MATLAB/Poblano. Shared oracle convergence and budgets replace the author's experiment-specific stopping rules.

## Work and stability

The complete controller, coefficient assembly, dense solve, search and history update run in C. Only oracle calls and optional diagnostics cross CPython. All persistent arrays and trial/search buffers are allocated once per solve.

The author's cached cross-inner-product strategy is retained, expressed in coordinates relative to the current accepted point. If `D_i=x_i-x` and `E_i=g_i-g`, cache `Q_ij=D_i'E_j`. Translation by `(s,y)` updates the cache by

`Qnew_ij = Q_ij - D_i'y - s'E_j + s'y`.

This costs O(n w + w²) rather than a full O(n w²) product each iteration. A full BLAS refresh occurs every 32 iterations; entries threatened by cancellation trigger direct difference-based assembly at the preconditioner point. Neither operation evaluates the objective. The acceleration is formed as a displacement before adding the base point.

The extension obtains the same LP64 SciPy BLAS/LAPACK capsules as XR, with the same strict floating-point compiler flags. Build metadata includes compiler, flags, ABI, source hashes, SciPy/NumPy versions and binary SHA. Compilation precedes experiment timing. No native code computes uncounted function values or gradients.

## Verification

`tests/test_oaccel_native.py` compares independent Python early trajectories for both preconditioners, the unregularized quadratic FOM/Galerkin identity, native convergence and oracle counts, nonfinite preconditioner halving, and exception identity. Nine line-search fixtures compare the complete sequence of native trial points against independent SciPy DCSRCH across starting steps and nonlinear curvature. A separate fixture verifies the warning fallback and its optional disabling. The SC executors use the author-compatible finite Armijo warning fallback for their initial seed, as detailed in `NativeSCAudit.md`. The shared backend compiles with `-Wall -Wextra -Werror -fno-fast-math -ffp-contract=off`.
