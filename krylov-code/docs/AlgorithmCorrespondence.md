# XR implementation and the verified algorithm

Practical XR/XR-F uses the article's observed ModelStep core with the recent
secant trial described in `PracticalVariant.md`. Its exact-real definition and
global stationarity adapter are in `krylov/XR/Practical.lean`; the shared
definitions are in `AlgorithmState.lean`, `AlgorithmModel.lean`, and
`Execution.lean`. The explicit midpoint diagnostic retains the original
spectral trial. The C execution and independent Python reference are tested
against these formulas. C, Python, NumPy, SciPy and the native linear algebra
are **not themselves formally verified**.

## One algorithm, composable mechanisms

`methods/xr_native.py::solve` is the registered executor for XR, XR-F and all
their ablations. `methods/xr.py::solve` is its independent Python reference.
`values=False` is XR;
`values=True` is XR-F. Both use recent positive secant curvature, the
Hermitian window test and the printed memory controller. Presets differ only
in their declared parameters: the primary memory policy is `m0=10, m_max=100`
(both capped by dimension); fixed memory means `m0=m_max`; full memory means
both equal dimension.

Nondefault options are explicit scientific ablations:
`window='positive'`, `probe=False`, `trial='lagged'`,
`trial='midpoint', floor=True`, or fixed memory. The Euclidean F split remains
an algebra option, outside the primary registry. `safeguard=False` is an instrument
for the conditional quadratic identity, whose theorem assumes an inactive
safeguard. It is not a practical benchmark preset.

The positive-only ablation changes the window selection gate only. A nonzero
F correction still passes its original Hermitian gate with the observed skew;
keeping that gate fixed makes this a single-factor comparison.

## Shared model correspondence and explicit trial policies

The Python column below names the readable reference implementation. The C
implementation uses the same parameters and policies, without selecting a
different algorithm for the native backend.

| Exact-real definition | Python | Formula / invariant |
|---|---|---|
| `algorithmInitialState`, `initialState` | `xr.initialize` | Actual initial `(f,g)`, `tau0=1/||g0||_inf`, `c1=epsilon*tau0`, `c2=tau0/epsilon` |
| `PairObservation`, `observedTrialPair` | `_xr_model.Pair.observe`, `xr.iterate` | Actual tested step and gradient difference, including a rejected probe |
| `retainNewest`, `rankWindow`, `rankDeletion` | `model_step` newest-first QR | Longest independent chronological suffix after the capacity restriction |
| `storedPairing`, `storedModel` | `C`, `latest(C)` | `C_ij=s_i^T y_j`, `T_ij=C_min(i,j),max(i,j)` |
| `modelDeletion`, `unrefutedSuffix` | `unrefuted_suffix` and `min(...,p-1)` | Reverse Hermitian Cholesky; retain the newest positive-curvature pair |
| `storedSplit` | `value_model`, `Pair.pairing` | `lambda_i=phi_i/C_ii-1/2` |
| `storedValueTerm` | `value_model` | Omit `12 lambda_i delta_i` when its absolute value exceeds `C_ii/2`; do not clip |
| `storedValueModel`, `correctedWindowPasses` | `value_model`, corrected Hermitian factorization | Corrected real model with **the original observed skew part** |
| `selectedModel`, model coefficients | `model_step`, `_symmetric_solve` | `w=-T_selected^{-1} S^T g`; virtual point and virtual gradient |
| `secantCurvature`, `freshCurvature` | Last positive physical secant scale | `rho=s^T y/||s||^2`, read before window deletions; cached when the window becomes numerically empty |
| `conjugacyDirection` | `model_step` | Solve `(Y^T S) beta=Y^T g_virtual`; manuscript singular-system fallback is `-g_virtual` |
| `practicalModel` | `model_step`, default `trial='secant'` | `u=Sw-(g^T d/(rho*||d||^2))*d`; no spectral accumulator, Ritz extrema, Schur solves or spectral floor |
| `updateBounds`, consistency coefficients, `adequacyFloor` | Explicit `trial='midpoint', floor=True` diagnostic | Original running Ritz interval and shifted-Schur rule, with uncorrected `T` even when F is enabled |
| Full-window / zero-direction branch | `model_step` | Return the projection correction with no missing-moment trial |
| `ModelResult.safeDirection` | `model_step` safeguard | Same descent/norm tests; fresh secant fallback clipped to the same fixed constants |
| `outerSearch` | `xr.iterate` | One finite rejected probe, one recomputation, then function-only rejected backtracking trials; gradient at acceptance |
| `appendPositive` | `Pair.observe` | Append only a strictly positive actual secant curvature |
| `PairObservation.transport`, `outerAdvance` | `Pair.transport` | Transport every retained observation by the accepted actual displacement |
| `updateCapacity` | `update_capacity` | Use the **first** ModelStep counts and total trial evaluations; floor-halving of odd capacities |

The capacity update deliberately has no extra test for safeguard activity,
curvature ratio, final model fullness, or total deletions in later calls.
Those would be different algorithms.

`Practical.lean::practicalModel_window` proves unchanged window bookkeeping;
`practicalModel_full` proves the full-window SS1/SS1-F correction. The actual
practical recursion is `practicalRun`. Its `practicalRun_global` proves square
summability of true gradient norms, convergence of their norms to zero, and
stationarity of every limit point under the same derivative, Lipschitz,
lower-bound and safeguard hypotheses as the general executor theorem. This is
an exact-real result, with no assumed spectral enclosure or local adequacy.
`PracticalQuadratic.lean` reuses faithful-window retention and the Galerkin theorem for the virtual CG point, gradient, direction and raw block-step decomposition. `PracticalQuadraticEventRun.lean` and `PracticalQuadraticTerminal.lean` derive those window hypotheses along the actual exact-arithmetic observation stream, with arbitrary accepted and rejected decisions and the stated nonzero trials. After the full set of independent pairs, the next full-window query is the minimizer; its Armijo acceptance is a separate conclusion for an Armijo parameter below one half. `PracticalQuadraticTranslation.lean` transports the execution to arbitrary initial points. Floating-point trajectories are covered by the implementation tests below.

The exact-real state's optional `bounds` slot carries `(rho,rho)` in that formal
adapter as a scalar cache; it has no spectral meaning in practical states.

`PracticalGrowthInitialRates.lean` and `EuclideanPracticalInitialRate.lean`
compose the literal practical executions with the conditional local theory
of Theorem 7.3 and Corollary 7.4. Their primitive sources specify local
derivatives, convergence, incoming independence, partial-trial adequacy and
fixed safeguard bounds. Unit acceptance, memory growth, chronological
SS1/SS1-F execution and physical R-orders are derived. Initially full memory
uses problem-only safeguard constants and needs no partial-trial adequacy.
The ordered declarations and their exact hypotheses are in
[the article map](../../krylov/ArticleMap.md).

## C execution and boundary

`native/xr_model.c` implements initialization, normalized pair storage, rolling
Gram/QR bookkeeping, rank and Hermitian suffix selection, both F gates, all
trial policies, safeguarding, covector transport and memory updates.
`native/xr_executor.c` implements the actual trial/acceptance/probe/backtracking
loop. Its state and workspaces are contiguous C allocations, released on every
normal or exceptional exit. The rejection loop uses the actual representable
displacement and compensated endpoint arithmetic, as in the reference.

`native/xr_bridge.c` only crosses the CPython boundary for the shared oracle,
optional diagnostics and compiled SciPy QR insertions/deletions. Fresh QR and
other numerical kernels call the installed SciPy BLAS/LAPACK through its
Cython capsules; capsule signatures are checked for the required LP64 integer
ABI. The observed pair arrays remain immutable during QR updates. No custom
line search, convergence test or uncharged gradient is introduced by the port.

The bridge copies gradients into C state and supplies owning point arrays to
the oracle. Thus an oracle retaining an argument cannot keep a dangling view
of a reused workspace. A function-only rejection requests only `f`; an accepted
scalar test acquires `g` at that same point. `Converged`, `Budget` and custom
observer exceptions propagate with their original identity after cleanup and
summary bookkeeping. `accepted_hook(x,f,g,info)` receives owning copies after
an accepted advance, with the window used to propose it, before insertion of
the new observation. It is absent in competitive runs.

`native/build.py` builds at module import, before the common oracle timer,
under an external source/compiler/ABI keyed cache. `-fno-fast-math` and
`-ffp-contract=off` preserve the specified arithmetic policy. Native build
metadata and the extension hash accompany the source fingerprint; failure to
build or an unsupported ABI is an explicit error. Details are in
[NativeSetup.md](NativeSetup.md).

The midpoint minimax theorem and floor-based local adequacy theorem are not
claimed for the secant or directional lagged policy. Conditional full-window
transition/rate statements retain their explicit independence and adequacy
hypotheses. No unconditional local fast-convergence claim is added.

The corrected directional lagged diagnostic learns only from an unshortened,
unsafeguarded model trial. It divides `unit_d^T(g_trial-g_virtual)` by the
actual projected displacement `unit_d^T(x_trial-x_virtual)`, including the
missing-direction step coefficient. Shortened trials do not satisfy that
comparison and do not update the estimate. Its clipping range consists of
individual active secant quotients, not generalized or historical Ritz bounds.

## Equivalent numerical algebra and caching

Each pair is represented in coordinates divided by `||s_i||`. The scalar
covector and defect are stored as `phi_i/||s_i||^2` and
`delta_i/||s_i||^2`. These diagonal congruences change neither the model, the
Hermitian certificate, the F gate, nor the physical step in exact arithmetic.
The Euclidean split ablation also transports its covector rather than
repeatedly subtracting nearly equal points.

`WindowAlgebra` reuses immutable Gram overlaps. It maintains the QR
factorization in newest-first order through column insertions and deletions;
a fresh QR is taken after 50 updates, or if an insertion is numerically
unresolved. In the midpoint diagnostic, shifted-Schur solves and Ritz use the orthonormal
basis: `R^-T T R^-1`. This avoids forming the potentially much worse conditioned
physical Gram matrix `S^T S`. Small model systems are diagonally equilibrated.
No unknown Hessian, extra oracle observation, ridge, eigenvalue replacement,
or pseudoinverse is used.

## Explicit floating-point policies and limits

1. **Numerical independence.** Unit-step QR diagonals must exceed
   `rank_multiplier * eps * max(n,p)`. In addition, the newest-first prefix
   must satisfy `rcond_1(R) > rank_multiplier * sqrt(eps)` (default multiplier
   32). The second check ensures that the *squared* condition number in the
   projected metric can be resolved from rounded secants. Oldest pairs are
   removed until both checks pass. Near dependence this is a numerical
   realization of rank cleanup, not literal decidability of independence
   over the reals. Consequently exact full-window identities are claimed
   only when no numerical deletion occurs. The chosen threshold is fixed
   across XR, XR-F and their ablations.
2. **Value noise.** The trapezoid defect uses compensated summation and is
   set to zero below `100 * eps` times the sum of endpoint-value and slope
   magnitudes. The exact-real executor has zero machine epsilon. This gate
   avoids interpreting cancellation error as third-derivative information.
3. **Nonfinite data.** A nonfinite trial is rejected and backtracked; it is
   not an informative probe. A finite informative first rejection triggers
   exactly one recomputation even if its secant curvature is nonpositive.
4. **Exhaustion is failure.** Oracle budget/time exceptions propagate.
   `maxbt` exhaustion, a trial indistinguishable from its anchor, or an
   unresolved linear-algebra failure returns an explicit stop reason. None
   counts as convergence. There is no accepted-step substitution or hidden
   relaxed target.
5. **Returned observations.** Performance targets are checked at actual
   evaluated points by the shared oracle. A virtual projected point is not
   reported as an evaluated gradient. On quadratics, reaching the minimizer
   virtually and then evaluating it are separate events.

## Independent checks

`tests/test_xr.py` and `tests/test_xr_variants.py` check physical Gram formulas
against independent dense solves, generalized Ritz bounds and Schur interval
containment, the full-dimension branch, longest rank/certificate suffixes,
capacity updates, transported anchor data, oversized F omission and rejection
of a corrected model whose real part is positive but whose Hermitian test
fails. Small resolved quadratic trajectories are checked against an independent
orthonormal-Krylov CG reference. Tests also verify pair-scaling invariance,
quadratic inactivity of F, and actual observed gradient targets for every
supported practical mechanism/ablation.

`tests/test_xr_native_model.py` reconstructs native models directly in physical
coordinates and checks warm rolling QR/Gram caches, including deletion of one
oldest column followed by insertion, independently of Python cache helpers.
`tests/test_xr_native_executor.py` checks complete reference/native trajectories
for the declared policies, actual oracle counts, function-only rejections,
accepted-window diagnostics, retained-array ownership, exception identity,
one-point budget exhaustion, invalid inputs and compilation outside solve.

## FC/RFC and the one-gradient theoretical controls

`methods/fc_exact.py` retains only FC and **one-correction** RFC. Its `direction`
is `windowDirection` from `RetainedSolve.lean`; retention is the prescribed
full/sliding/restarted policy of `Windows.lean`. The direction solve is required
to exist; a failure is reported instead of clearing the window and silently
restarting. `correction_displacement` follows `RFC.lean::rfcCorrection` with
count one and `RFCArray.lean::rfcCorrection_array`: the normalized skew defect
is tested on the **retained old window**, while the enlarged latest-information
matrix supplies the correction. Ordinary RFC invokes the inverse without
adding a positive-definiteness gate or a function-decrease gate. Its separate
`gamma_gate` option is the explicitly named conditioned/gated RFC rule.

`fc_exact.operator_cycle` executes the linear observation protocol of
`Protocol.lean::methodAdvance`: it observes only `z=A_k d`, computes the
algebraic line length, and observes each nonfinal correction under `B_k`.
At a terminal correction, the returned true gradient is an **external semantic
error assessment**, not an algorithm observation. No subsequent decision reads
that terminal diagnostic. `xrbench/theory.py` generates the corresponding
small variation experiment; its costs are separate from objective-oracle
performance profiles. The log explicitly records this distinction.

For fixed objective controls, `search='quadratic'` invokes an explicitly counted
Hessian-vector query and then evaluates the real endpoint. It therefore has
additional information and a different actual-query cost from the abstract
one-probe accounting. `search='root'` instead uses a counted Brent solve of the
directional derivative with declared relative tolerance; this is a numerical
approximation to exact search, not an exact-arithmetic implementation. Neither
is used as a practical competitor under the main first-order protocol.

`methods/xrfc.py` is a minimal realization of `OneGradient.lean::xrfcMethod`.
It contains the virtual Galerkin solve, conjugacy solve, prescribed nonzero
trial and one actual endpoint query. There are no rejection loops, empirical
restarts, defect-based suffixes or safeguards. The virtual output is marked
`evaluated=False`; completing a theoretical cycle is not a gradient-target
success. The exact identity for arbitrary nonzero trials remains an
exact-arithmetic assertion. Extremely short trials can make the stored step
basis unresolved in double precision; these required model solves have no
numerical rank deletion that would change this theoretical policy. Independent
trajectory fixtures use well-resolved nonzero trials.

## Acceptance and actual observed displacement

The executor evaluates acceptance as
`finite(ft,gt) and slope < 0 and ft <= f + sigma*slope`, where `slope` uses the
actual tested displacement. This is exactly the same predicate over the reals:
`krylov/XR/BacktrackingDescent.lean::accepted_iff_armijo` proves equivalence to
the printed quotient test under a positive trial length and negative slope.
The quotient is still computed for rejected-trial backtracking and diagnostics.
No epsilon is added to the acceptance inequality, no target is relaxed, and no
extra oracle observation is taken.

The two arithmetic expressions are **not claimed to be identical in binary64**.
If an objective has a large constant offset, two endpoint values can round to
the same number: the quotient form then gives exactly 2 and rejects, whereas
the directly evaluated Armijo right-hand side can round to the current value.
Using the direct form avoids this cancellation and matches the standard
computational form of Armijo. The exact-real proofs do not certify binary64
acceptance or monotonicity below the objective's rounding resolution.

After constructing the representable query `xt = x + t*u`, the executor sets
`s = xt - x`. That same actual displacement is used for the observed secant,
its value defect, the acceptance slope, and all accepted anchor transports.
Over the reals `s=t*u`; in floating point a tiny intended component may round
away at a large anchor. Pairing the intended vector with a gradient observed
at a different representable point can create a spurious secant. Backtracking
continues to scale the original model direction by the same quotient rule.

Independent regression tests cover a quadratic with a `1e16` constant offset
and assert an unchanged actual gradient target. A separate large-anchor fixture
checks, without invoking ModelStep, that the stored step, gradient difference,
acceptance slope and transported old/new covectors all correspond to the one
actual endpoint query. The existing independent physical-Gram, Ritz, Schur,
CG, memory and F-gate checks remain in force.

## Compiled competitor execution

`methods/competitors_native.py` dispatches MS-L-BFGS, SC-MSS, SC-SR1 and
O-ACCEL-B to their complete C controllers. `native/competitor_bridge.c` binds
the same shared oracle; `competitor_common.c` supplies More–Thuente arithmetic
and the common BLAS/LAPACK ABI. The C compiler policy and external build
cache match XR. The four ports are our independent implementations of the
published methods, not author-native distributions. L-CG_DESCENT retains
its author's C executor; L-BFGS uses SciPy's compiled L-BFGS-B descendant.

The SC implementation follows the author software and published equations.
`native/sc_native.c` uses the current curvature plus q prior observations,
the published dense MSS initialization, the author compact SR1 base-vector
gate and initial search defaults. Source details, numerical choices and independent tests are described in [NativeSCAudit.md](NativeSCAudit.md). The readable Python SC controllers provide independent differential references. Formal statements about an update or
model do not certify these full floating-point competitor executors.
