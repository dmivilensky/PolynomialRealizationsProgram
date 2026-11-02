# Model conditioning and numerical behavior

The midpoint ablation accumulates physical-metric Ritz bounds. The practical
secant trial uses a recent positive scale instead; the following example
explains the distinction. Both rules retain the same observed secant model.

## Bounded secant operators can produce an arbitrarily large latest model

Let \(h>0\), with chronological observations in \(\mathbb R^2\),

\[
s_0=e_1,\quad y_0=\tfrac32e_1,
\qquad s_1=e_1+h e_2,\quad y_1=s_1.
\]

These are valid secant observations \(y_i=A_i s_i\) for the positive operators
\(A_0=\tfrac32I\) and \(A_1=I\), both with norm at most \(3/2\). Here the
operators encode the individual observed actions; no identity of their
chronological latest-information model with either operator is assumed.
For an actual objective, the analogous individual operators are averaged
Hessians along the observed segments. This example is an exact observed-data
construction, not a reconstruction of the Hessian of a particular CUTEst task.

The physical Gram and observed pairing matrices are

\[
G=S^\top S=
\begin{pmatrix}1&1\\1&1+h^2\end{pmatrix},\qquad
C=S^\top Y=
\begin{pmatrix}3/2&1\\3/2&1+h^2\end{pmatrix}.
\]

XR's latest model and skew defect are therefore

\[
\bar T=\begin{pmatrix}3/2&1\\1&1+h^2\end{pmatrix},\qquad
D=C-C^\top=\begin{pmatrix}0&-1/2\\1/2&0\end{pmatrix}.
\]

The two steps are independent for every \(h>0\). The default Hermitian test
also passes exactly:

\[
\bar T+iD=
\begin{pmatrix}3/2&1-i/2\\1+i/2&1+h^2\end{pmatrix},\qquad
\det(\bar T+iD)=\tfrac14+\tfrac32h^2>0.
\]

Its first principal minor is \(3/2>0\), so neither pair is removed by the
mathematical certificate. Nevertheless,

\[
\det(\bar T-\lambda G)
=(1-\lambda)\bigl[\tfrac12+(\tfrac32-\lambda)h^2\bigr],
\]

and the generalized Ritz values are

\[
\lambda_-=1,\qquad
\lambda_+=\tfrac32+\frac1{2h^2}.
\]

Thus uniformly bounded **different observed operators do not imply a bounded
latest model in the physical step metric**. Even the simple vector
\(c=(1,-1)^\top\) has model Rayleigh quotient
\((c^\top\bar T c)/\|Sc\|^2=1+1/(2h^2)\).
The large value comes from a near cancellation of physical steps while their
chronologically combined observations retain nonzero model energy. This is
consistent with the article's distinction between an observed defect test and
a bound on hidden curvature error.

At \(h=10^{-5}\), the exact upper Ritz value is approximately
\(5\cdot10^9\). With inflation \(\varpi=2\), the implementation
updates the running interval to

\[
(\widehat\mu,\widehat L)
=\left(\tfrac12,\ 3+10^{10}\right).
\]

The fixed numerical rank test retains these two independent steps. Its
one-sided QR reciprocal condition estimate is resolvable at this scale; no
rounding error, failed certificate or missing square root is needed to produce
this large upper estimate. `test_bounded_changing_secants_can_have_large_certified_ritz_range`
checks the exact formula, the passing certificate, and persistence of the
running upper estimate when a later window has ordinary curvature.

## Accumulated spectral estimates

The spectral rule updates

\[
 \widehat\mu\gets\min\{\widehat\mu,\lambda_-/\varpi\},\qquad
 \widehat L\gets\max\{\widehat L,\varpi\lambda_+\}.
\]

Deleting a window leaves these bounds unchanged. A large model Ritz value
can therefore make later missing-direction trials conservative. A certificate
for the observed Hermitian model supplies different information from a true
Hessian enclosure. The fresh positive-secant policy in
[PracticalVariant.md](PracticalVariant.md) avoids this spectral accumulator.

Ritz values use the pair `(Tbar,S.T@S)` or the equivalent QR congruence
`R^{-T} Tbar R^{-1}`. Schur endpoints use the uncorrected model even in XR-F.
The scalar `rho` corresponds to supplied directional curvature
`c_hat=rho*||d||²`. Pair normalization and reordering preserve these identities.

## Finite precision

Acceptance evaluates the direct Armijo inequality using the actual
representable displacement `x_trial-x`. The real-arithmetic quotient criterion
is equivalent under negative slope and positive trial length; direct evaluation
avoids cancellation from a large constant objective offset. The same actual
displacement defines the observed secant, endpoint defect and transported
covectors. The numerical rank and endpoint-noise policies are specified in
[AlgorithmCorrespondence.md](AlgorithmCorrespondence.md).

Uniform independence and trial adequacy remain assumptions of the conditional
full-window local rates. A numerical rank test does not certify those
hypotheses for every benchmark trajectory.

## Observed regimes

The controlled grid shows increasing gradient-cost advantages with conditioning,
including substantial nonlinear perturbations. On CUTEst, XR has high coverage
and competitive gradient cost; L-CG_DESCENT retains the clearest time advantage.
XR solves 237 of 257 instances, compared with 238 for L-CG_DESCENT.

All eight methods reach the target on all 24 logistic objectives. At each of
the two weaker regularizations, XR or XR-F attains the smallest gradient count
and elapsed time on every dataset. At the strongest penalty, MS-L-BFGS often
uses fewer gradients. The F correction has a modest average logistic benefit
and a problem-dependent cost/coverage tradeoff on CUTEst.

All 120 full-memory local runs reach the accepted-iterate error target with
full windows and inactive safeguards. Their cohort costs are similar for XR
and XR-F; individual trajectories distinguish the value correction's effect.

The figures and tables use the common protocol in
[ExperimentProtocol.md](ExperimentProtocol.md). Measured times describe one
serial run per method/problem; close differences require cautious interpretation.
