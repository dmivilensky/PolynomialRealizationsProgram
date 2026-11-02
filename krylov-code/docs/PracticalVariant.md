# Practical XR trial and ablations

For retained pairs `S,Y`, XR builds the chronological latest model, tests the
longest admissible suffix, and forms the virtual subspace correction `Sw` and
conjugate direction `d`. Its missing-direction trial is

\[
 u=Sw-\frac{g^\top d}{\rho\|d\|^2}d,
 \qquad \rho=\frac{s^\top y}{s^\top s}>0,
\]

where the scalar is updated from the most recent observed pair with positive
curvature. Until such a pair is available, the initialized positive scale is
retained. The fallback also uses the recent scale, clipped to the fixed
safeguard bounds. An empty window uses this same scale.

## Acceptance and information

The model direction is checked against the gradient-related safeguard.
Armijo uses the directly evaluated sufficient-decrease inequality. One finite
informative rejected trial supplies a gradient and may update the model.
Subsequent rejected backtracking points request only function values; a
gradient is acquired at acceptance. Recorded secants use the actual
representable displacement between the evaluated points.

The positive-secant trial needs neither generalized Ritz extrema nor Schur
endpoint solves. Pair normalization, incremental QR, maintained Grams and
preallocated storage reduce model work without changing the exact model.

## Function values and memory

XR-F applies the model-metric value correction when its gate passes. Endpoint
trapezoid defects use compensated arithmetic; cancellation-sized defects are
set to zero. The window test, virtual step and memory controller are shared
with XR. The primary initial memory is `min(10,n)`, growing to `min(100,n)`.

## One-factor ablations

| Variant | Mechanism changed |
|---|---|
| F-off | Omit the value correction; this is XR. |
| Fixed memory | Cap retained storage at ten pairs. |
| Positive-only | Test positive model curvature without the Hermitian defect gate. |
| No-probe | Omit the gradient at the informative rejected trial. |
| Midpoint | Use the spectral interval, historical bounds and adequacy floor. |
| Directional lagged | Estimate missing curvature from the preceding eligible trial. |

The directional estimate divides
`unit_d.T @ (g_trial-g_virtual)` by
`unit_d.T @ (x_trial-x_virtual)`. It is updated only for an unshortened,
unsafeguarded trial and clipped to the current individual positive secant
quotients. The denominator includes the actual missing-direction coefficient.

## Mathematical guarantees

The arbitrary-trial quadratic identities, full-window SS1/SS1-F correction
and safeguarded global stationarity apply with their stated assumptions.
The conditional local transition retains uniform independence and trial
adequacy; its literal execution and both F splits are connected to the
SS1/SS1-F rates in `PracticalGrowthInitialRates.lean` and
`EuclideanPracticalInitialRate.lean`. The interval midpoint has its separate information-minimax and
floor-based adequacy results. See
[AlgorithmCorrespondence.md](AlgorithmCorrespondence.md) for the exact-real
statements and their implementation counterparts, and
[NumericalFindings.md](NumericalFindings.md) for physical-metric conditioning.
