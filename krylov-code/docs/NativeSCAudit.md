# SC-MSS and SC-SR1 implementation

The C implementations use compact symmetric models, separable shape-changing
infinity subproblems and a trust-region controller. The formulas and numerical
choices below identify their relationship to the published MATLAB algorithms.

## Primary sources

- Brust, Erway and Marcia, *Shape-changing trust-region methods using
  multipoint symmetric secant matrices*, Optim. Methods Softw. 39(5)
  (2024), 990–1007, [DOI](https://doi.org/10.1080/10556788.2023.2296441),
  [open paper](https://arxiv.org/abs/2209.12057).
- [Author SCMSS repository](https://github.com/johannesbrust/SCMSS),
  source routines `ALGS/LMSS_SC.m`, `ALGS/sc_mssm_infty.m`, and
  `EXPERIMENTS/EX_COMP_LMSSM_LSR1_SCINF_DENSE/driver_EX_COMP_LMSSM_LSR1_SCINF_DENSE.m`.
  That driver explicitly selects SC-INF-D (`whichDenseInit=4`), m=3,q=5.
- Brust, Burdakov, Erway and Marcia, *Algorithm 1030: SC-SR1: MATLAB
  Software for Limited-memory SR1 Trust-region Methods*, ACM TOMS 48(4)
  (2022), Article 48, [DOI](https://doi.org/10.1145/3550269),
  [open paper](https://arxiv.org/abs/1607.03533).
- [Published ACM software archive](https://calgo.acm.org/1030.zip):
  `1030/CPP/ALGS/LSR1_SC.m`, `sc_sr1_infty.m`, and the experimental drivers.
  Despite the archive directory name CPP, these inspected algorithms are MATLAB.
  The selected variant is SC-INF, Init.2, m=5,q=7.

## Source-to-C correspondence

| Component | Source | Production implementation |
|---|---|---|
| Chronological lower-triangle compact pairing | MSS compact formula (15); SR1 compact formula (4) | `cn_sc_model`: mirrored lower triangle of normalized S'Y |
| MSS correction | `LMSS_SC.m`, `M` blocks | `[-zeta W-W X W,W; W,0]`, Psi=[S,Y] |
| SR1 correction | `LSR1_SC.m`, `invM` | Psi=Y-gamma S; K=lower(S'Y)+strict-lower(S'Y)'-gamma S'S; linear solve K Z=R' |
| Model eigenbasis | `sc_*_infty.m`, ComputeSpectral | pivoted thin QR, reduced symmetric eigensolve, P=Q U |
| Independent step selection | MSS raw memory and independent normalized step subset | raw m-window retained; pivoted QR selects a chronological independent subset |
| Parallel subproblem | SC-SR1 Algorithm 3; MSS (19)–(22) | independent exact scalar box minima |
| Complement subproblem | same source | isotropic ball minimizer without constructing complement basis |
| Model decrease | author `pred=-(gs+0.5*sBs)` | actual -g'p-p'Bp/2, reconstructed independently in tests |
| Accepted/rejected observations | both author outer loops | every finite trial advances curvature history and is eligible for model storage |
| Radius controller | author experimental constants | accept rho>9e-4; expand by2 for rho>.75 and ||p||>.8delta; shrink by.5 for rho<.1 |
| Initial search | both source default parameter blocks | More–Thuente, alpha0=1, ftol=1e-4, gtol=.9, xtol=1e-6, maxstep5, maxfev3000 |
| Initial radius | both outer loops | twice first accepted Euclidean step length |

The maximum-history initialization uses **the current curvature and q previous
values**, then advances the q-entry ring. Initial history contains gamma=1;
the first initialized maximum is inserted, as in the author code. Undefined
`yy/sy` advances the history with an unavailable entry and retains the last
usable scale if necessary. MSS dense complement curvature starts at one,
then changes only when a subsequent observation has positive `s'y`, using
that observation's `yy/sy`. The independent Python references use the same formulas.

### Initial search warning and model seed

Author `cvsrch_INTF.m` returns its evaluated point on a search warning as
well as on strong-Wolfe success. In particular, its code5 reports a decreasing
point at the maximum step5 even when the curvature condition is unmet.
Both author outer loops adopt that point as their initial trust-region seed.
Requiring strict strong Wolfe here would instead stop on flat positive
objectives before forming any model, including CUTEst FLETBV3M.

The C and independent Python SC initial searches therefore retain their best
finite Armijo point on a warning. At the decreasing upper-bound case this is
the author seed. For rounding or iteration-limit warnings, this best-decrease
choice is an explicit numerical policy: author code returns its final point,
and code6 prevents its later outer loop. We do not assert identical continuation
on all warning codes. The seed is an actually evaluated, decreasing point;
there is no uncharged observation or relaxed final gradient target. The
non-SC Python search retains its strict-Wolfe default.

### SR1 storage gate

The selected author's compact implementation gates on the **base vector**
`v=y-gamma*s` at the newly computed initialization, rather than recomputing
the sequential update residual `y-B_current*s`. The experimental driver sets
`SR1tolAdj=1e-10`, with `SR1tol=1e-8`. We use its coherent later-iteration test

```
abs(s'v) > 1e-8 * max(||s|| ||v||, 1e-10).
```

The gate uses physical, unnormalized observations. Pair normalization occurs
only inside the model algebra, so it cannot change the absolute floor.
Old observations are not regated when gamma changes, matching the compact
source implementation. This gate alone does not prove every subsequent
compact system nonsingular; a failed factorization is reported as a numerical
model stop, rather than introducing a ridge.

The source's **first-pair** condition instead reads
`SR1tol < abs(s'v)*||s||*||v||` (LSR1_SC.m line489). Its multiplicative scaling
is inconsistent with the normalized condition documented by that same file
and used later. We use the coherent later gate at the first pair as well.
This is a deliberate correction, not a claim to execute that anomalous line.

## Finite precision and interface choices

- Both solvers use the same SciPy LP64 BLAS/LAPACK capsules, `-O3`, strict
  floating-point flags and compiler as XR. Model/controller/search/history
  execute in C; the shared oracle remains the same Python interface.
- Pair normalization, pivoted QR and triangular solves replace the author's
  Gram-LDL constructions. Relative QR rank tolerance is 1e-10. The raw MSS
  window is retained even when dependent; its model uses independent columns.
- For an empty compact model, we solve the same isotropic ball subproblem;
  the author subproblem routine instead returns a unit steepest-descent vector
  before checking radius. The C choice preserves the stated feasible problem.
- Eigenvalues are retained rather than zeroed at the author's absolute
  `sqrt(eps)` threshold. This avoids an absolute Hessian scale in the
  mathematical subproblem. Flat scalar quadratics choose zero, an exact
  minimizer; negative-curvature/zero-gradient ties choose a feasible endpoint.
  The complement hard case chooses a coordinate with minimal projection.
- All production workspace is allocated once per solve. No dense n-by-n
  Hessian or complement basis is stored; no per-iteration allocation occurs.
- Shared stopping targets/budgets replace author infinity-norm termination.
  Function and gradient calls use exactly the shared oracle; initial search
  and each trust trial request `fg` once. Native callback exceptions unwind
  without retry or conversion to acceptance.
- Radius collapse uses `100*eps*max(1,||x||)` rather than the author's absolute
  1e-18/1e-20. A mathematically nonzero but unrepresentable step is a stop.
- The unchanged Euclidean and line-search Python variants remain test algebra
  references; the benchmark selects the source-audited SC variants.

## Verification

`tests/test_sc_native.py` calls the actual production C model and subproblem,
then compares against independent dense rank-two MSS and rank-one SR1
recursions, including indefinite matrices. Tests cover simultaneous pair
rescaling, dependent MSS windows, exact scalar/ball subproblem minima,
negative-curvature complement hard cases, full-loop quadratic convergence,
original callback exception preservation, the author initial-boundary warning
seed on a flat positive quadratic, and full evaluated trial sequences
against the source-aligned independent Python controller. A first-model
fixture separately reconstructs gamma, dense initialization, model decrease,
ratio and radius directly from the initial physical observation and the
published equations. This catches controller/model mismatches without using
the Python spectral model as the expected result.

The C implementation follows these mathematical components; dense and trajectory
tests check their floating-point realization.
