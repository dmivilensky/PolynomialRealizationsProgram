# Experimental protocol

All methods use the same objective, initial point, observation cache, stopping
target and resource limits within a cohort. Parameters are fixed across
problems; their sources are in [PresetRationale.md](PresetRationale.md).

## Objectives

The controlled quadratic family uses dimensions 20 and 100, condition numbers
100 and 10000, and three seeds. The positive definite matrix has a geometric
spectrum. The minimizer is zero and the initial base-energy norm is one.
Nonlinear perturbations use

\[
 f_\varepsilon(x)=\tfrac12x^\top Ax+
 \varepsilon\sum_j(e^{a_j^\top x}-1-a_j^\top x),
 \qquad a_j=A^{1/2}u_j,\quad\|u_j\|=1.
\]

The complete nonlinear grid uses `n=100`, three seeds,
`kappa in {100,1000,10000}` and `epsilon in {0.001,0.1,1,10}`.

CUTEst supplies 257 instances from 149 families. Four nonlinear profile groups
contain 77/43 sum-of-squares and 67/61 general objectives, split at dimension
300. Nine classified quadratics are additional controls. Classification uses
objective structure and actual dimension; a sum of squares can be nonconvex.

LIBSVM supplies a9a, w8a, covtype.binary, madelon, gisette, epsilon,
rcv1.binary and real-sim. All observations in each training set are used.
Normalize each nonzero feature row to unit Euclidean norm and solve

\[
 F_\lambda(w,b)=N^{-1}\sum_i\log(1+e^{-y_i(a_i^\top w+b)})
 +\tfrac\lambda2(\|w\|^2+b^2).
\]

The intercept is regularized. Three penalties `0.01,0.0001,0.000001` and one
zero start give 24 smooth strongly convex objectives. Stable `logaddexp` and
`expit` evaluate the function and analytic gradient. Dense and CSR designs
share the same interface. Raw files and prepared arrays stay in the external
`XR_LIBSVM_DATA` cache; receipts check their identities.

## Target and costs

Success requires an actually observed gradient satisfying

\[
 \|g(x)\|_2\le10^{-8}\max\{1,\|g(x_0)\|_2\}.
\]

On nonconvex objectives this measures first-order stationarity. Initialization
and rejected probes count. Profiles use actual gradient evaluations and
elapsed solver time. Function and gradient requests are separate; a joint
request increments both evaluation counts. The common four-point exact cache
charges an observation slot once while its point remains resident.

The charged-point limit is 100000. CUTEst and controlled tasks have 120 solver
seconds; logistic tasks have 300. Budget exhaustion, numerical stops and
search failures retain failure status unless the common target was reached.

Runs are sequential with one BLAS thread. Problem construction, data warm-up,
module loading and native compilation precede timing. Solver allocation,
model algebra, searches, callbacks and evaluations are timed. Each pair
contributes one measured run. Close times require cautious interpretation.
Implementation languages and numerical choices are stated in
[CompetitorAudit.md](CompetitorAudit.md).

## Performance profiles

For scheduled problems `P`, methods `S` and successful cost `t`, define

\[
 r_{p,s}=\frac{t_{p,s}}{\min_{u\in S}t_{p,u}},\qquad
 \rho_s(r)=|P|^{-1}\sum_{p\in P}\mathbf1\{r_{p,s}\le r\}.
\]

Failures and missing observations have infinite ratio. All-method failures
remain in the ordinary denominator. Exact ties all count at one. Missing jobs
mark a comparison as incomplete.

Companion empirical-logit panels condition on problems solved by at least one
method. With conditional cohort size `N` and `k_s(r)` qualifying successes,

\[
 z_s(r)=\log\frac{k_s(r)+1/2}{N-k_s(r)+1/2}.
\]

Ticks show the original fractions `k_s/N`. Both endpoints are finite and the
complete base-two horizontal ratio range is retained. Bright contrasting
colors, a few dash styles and sparse hollow markers identify the methods.

## Additional studies

Six one-factor ablations use 64 CUTEst starts, 16 per nonlinear group.
Primary XR/XR-F observations are reused explicitly as reference rows.
[PracticalVariant.md](PracticalVariant.md) defines each modification.

The settings study uses 16 starts, four per group, selected by sorting hashes
of `"tight:" + problem`. It varies the memory parameters listed in
[PresetRationale.md](PresetRationale.md). The same starts are tested at
relative tolerance `1e-10`. Full-matrix BFGS-SP uses Shanno–Phua scaling and
More–Thuente search on 149 small CUTEst cases and twelve quadratics.

The local study uses `n in {5,10,20}`, `kappa in {10,100}`, ten seeds,
`epsilon=0.1`, initial base-energy norm `0.03` and full memory `n`.
Its accepted-iterate target is relative stationary-Hessian error `1e-12`.
The analytic Hessian is diagnostic information and is not supplied to the
solver. Every accepted point, used window and safeguard event is recorded.

## Summaries

Paired ratios are geometric means on joint successes, with exclusive
successes counted separately. Means over each method's successes use that
method's own denominator. Failed runs receive no finite replacement cost.
Constant table columns move to the caption. The perturbation heatmap covers
every condition/perturbation cell and seed; local curves retain every accepted
iterate of two fixed dimension endpoints and a fixed common seed.

The full set comprises 3545 actual computations: 2976 main, 160 settings,
289 reference/accuracy and 120 local runs. The main comparison has 128 exact
aliases; settings have 80 explicit primary-result references. These reused
rows are counted separately from computations.

Source: Dolan and More, *Benchmarking optimization software with performance
profiles*, Mathematical Programming 91:201–213 (2002),
[DOI](https://doi.org/10.1007/s101070100263).
