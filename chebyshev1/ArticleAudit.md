# Manual correspondence audit, 5 November 2026

All identified correspondence obligations R1–R7 are resolved. The repaired active
mathematics of the main article and supplementary has undergone two manual
passes against the actual Lean definitions, hypotheses, conclusions and proof
chains. Corrections found in the second pass were reread after editing. A
subsequent adversarial recheck found and corrected the additional text bindings
and boundary qualifications recorded below; the earlier review had missed them.

The inventory covers 28 numbered main statements, 6 numbered supplementary
statements and 19 groups of unnumbered mathematics, including Appendices A–F
and both algorithms. [ArticleMap.md](ArticleMap.md) gives the individual scopes;
[Article.lean](Article.lean) checks its 424 listed signature references in order.
Commented text, experimental observations, floating-point performance and open
optimization problems are excluded from the proof-coverage claim. Manuscripts
were read manually: no TeX/PDF parser, statement extractor or automatic manuscript
comparison was used. The inventory checker reads the map and Lean sources only.

## Resolved findings

**R1 — Translated physical execution.** Initial normalization alone does not make
a general linear-memory query translation consistent. The manuscript now states
coefficient-level affine consistency and uses centered memory states.
[Affine execution](Realization/AffineExecution.lean) proves the center product
identity, actual physical execution for arbitrary time-dependent Hessians, the
physical-output error identity, constant-H residual action and p_N(0)=1.
[Concrete methods](Realization/AffineMethods.lean) derives consistency for every
advertised method. [Degree](Realization/Degree.lean) and
[realization minimax](Realization/Minimax.lean) also derive the actual degree bound
and interval minimax lower bound. The existing raw Realization record is retained.

**R2 — Universal quantifier and positive fibre.**
[Universal gain](Realization/UniversalGain.lean) proves the endpoint mass and gain
lower bound for every terminal-Chebyshev-exact realization, of arbitrary memory
and arbitrary coefficient signs. Its signed profile has sum N²; the exact energy
gap is the sum of (d_s-N)². Flatness is necessary for equality in the gain bound.
No positivity or Jacobi representation is assumed. The positive resolvent
interpretation is recovered by [the Jacobi bridge](Jacobi/OperatorL2.lean).
Probability-weight parametrization, Schur upper bounds and the positive converse
remain explicitly restricted to the positive fibre; terminal exactness supplies
spectral containment. [Stepsize profiles](Stepsize/EndpointProfile.lean) proves the
full reciprocal-gap profile for the actual temporal permutation.

**R3 — Finite drift.** The summary now retains EndpointMax. The order bounds and
static-shift attainment prove the three exact Chebyshev bounds under that
condition; the cosh envelope is a separate upper estimate. Both advertised
momentum families satisfy the condition.
[Expanded maximum](Chebyshev/ExpandedMaximum.lean) additionally proves the exact
terminal maximum on the enlarged interval; it is distinguished from the drift
*difference*, which subtracts epsilon_N.

**R4 — Heavy-ball optimality.**
[Heavy-ball optimality](Background/HeavyBallOptimality.lean) minimizes the actual
supremum of characteristic-root moduli over all curvatures in the interval and
all real constant stepsize/momentum pairs. It proves boundedness of that root
set, the universal lower rate, attainment and the unique minimizing parameters.
The earlier coefficient-limit theorems therefore converge to a proved optimizer,
rather than merely to formulas named optimal.

**R5 — Finite stochastic inputs.**
[Finite scalar noise](Stochastic/FiniteScalarNoise.lean),
[finite spectral moments](Stochastic/FiniteIndependentSpectral.lean),
[finite matrix runs](Stochastic/FiniteMatrixRun.lean) and
[finite gossip](Stochastic/FiniteGossip.lean) operate on the original probability
space with moment, independence and activation assumptions only for s<N.
Any zero continuation is proved independent on that same space; global unit
variance or global iid continuation is not assumed. IID attainment permits a
whole pair of maximizing eigenspaces, including multiplicities and within-block
correlations. The actual matrix execution has the stated spherical variance and
nonnegative fourth-order remainder.

Finite gossip proves the exact p/(1-p) Gamma prefactor and a nonnegative remainder
bounded by 4p² times a deterministic constant independent of the sampling law.
Its asymptotic interface permits the probability measure to vary with p.
[Gossip scaling](Stochastic/GossipScaling.lean) proves pathwise equality of the
actual normalized and unrescaled-weight runs on (1-p)[mu,L], and equality after
subtracting their corresponding nominal runs. Thus the exact variance, Gamma
and remainder transport, not just a formal terminal polynomial. The text states
independence across edges and steps and identifies the consensus target without
asserting convergence from average preservation alone.

**R6 — Operator-norm time-l2 bound.**
[Operator l2](Realization/OperatorL2.lean) derives the matrix-response factorization
from scalar polynomial kernel factorization, then proves the actual Euclidean
operator-norm bound A_N times sqrt(sum_s opNorm(E_s)²) under common maxima.
[Jacobi specializations](Jacobi/OperatorL2.lean) supplies the advertised families.
Neither the matrix identity nor the desired norm conclusion is an input premise.

**R7 — Squares and small-index conventions.** Sine and prefix prose consistently
use squared off-diagonal couplings when referring to 1/4. Exceptional prefix and
reversed-prefix couplings have explicit index ranges. P_0=1 is separated from
P_s=2^(1-s)T_s for s>=1. Both endpoint-profile formulas state their nonexceptional
ranges. The scaled C_N limit has tau>0, and the 14% variance comparison is stated
asymptotically. Other boundary wording includes the n>=1 product formula, the
continuous extension of U_n at sin(theta)=0, precise gain units and the separate
zero-drift amplification convention.

## Two-pass review

Both passes inspected actual proof hypotheses and mathematical constructions,
not merely theorem names or successful #check commands. The second pass rotated
the reviewed areas; Appendix C also received two separate final reads. Every
finding was corrected and the affected passage reread.

| Area | Pass A | Pass B |
| --- | --- | --- |
| Abstract/introduction, Sections 2–5, Appendices A–C | Matched after scope/index corrections | Matched; affine execution, arbitrary-memory bound, minimax, heavy-ball, Favard, CG and operator bound checked |
| Section 6 and Appendix D | Matched after square/index corrections | Matched; signed residues, reversal, all-block maxima, hard-edge uniqueness and limits checked |
| Section 7 and Appendix E | Matched with EndpointMax | Matched; actual confinement, restarts, weighted second variation, cubic attainment and scaling limits checked |
| Section 8 and Appendix F | Matched after finite-input extensions | Matched; actual runs, both filtrations, PSD homogeneous quadratic covariance, full-vector Taylor and gossip scaling checked |
| Supplement S1–S4 and Algorithms S1/S2 | Matched | Matched; N=1, finite variance polynomial, both radial cases, rounded horizons/budgets and actual nonlinear algorithms checked |

No desired expansion, invariance, factorization or optimality conclusion is
assumed in place of the reviewed construction. The remaining numerical weight
path samples and finite sine/prefix ratios are empirical observations; a global
gain optimizer on the fibre and arithmetic-rounding stability remain open claims,
not silently counted as formal theorems.

## Subsequent adversarial recheck

The user requested another check. This pass started from the active manuscript
without treating this map or the previous successful build as evidence of
semantic correspondence. Actual proof bodies, small horizons and explicit
counterexamples were examined. It found the following additional textual issues;
all were corrected and the changed passages reread.

- **Class of gradient methods, Section 2.** Arbitrary affine mixtures of a
  point and gradients need not preserve a translated minimizer. For example,
  x_1=(x_0+grad f(x_0))/2 with f(x)=(x-1)^2/2 and x_0=1 gives x_1=1/2.
  The preliminary statement now explicitly uses the affine-consistent
  realizations of Definition 3.1, matching the physical-execution theorem.
- **Initial-coefficient uniqueness, Sections 2/4.** At x_-1=x_0, replacing
  (alpha_0,beta_0)=(1,0) by (2,1) changes no iterate. The two-term convention
  now explicitly fixes beta_0=0. Lean's `initial_unique` determines gamma_0;
  `coefficients_unique` determines all coefficients only for 1<=t<N. The
  unused initial a/b record fields are not claimed to be determined.
- **Positive horizons and proof endpoints.** The paper now fixes N>=1;
  otherwise its literal 2^(1-N)T_N normalization fails at N=0. The generic
  Lean `monicChebyshev` already treats zero correctly. Appendix D's estimate
  b_s>=1/(2 sqrt(s)) now states s>=1 and handles F_0=1 separately.
- **Individual kernels versus temporal aggregates, Section 3.** Only the
  diagonal sum over time is determined by the terminal polynomial. For
  reordered stepsizes, individual endpoint kernels are permuted, whereas their
  temporal l2 norm is unchanged. Both explanatory sentences now say this
  explicitly, matching `kernel_sum_derivative` and `endpoint_square_sum`.
- **Actual Hessian, Corollary 8.1(a).** The statement now explicitly requires
  stationarity and H=Hessian f(x*), with the stated spectral bounds. If
  f(x)=a x²/2 but H differs from a, the claimed remainder would contain
  -gamma_0(a-H)e_0, a linear term. The actual-objective Lean theorem already
  uses the true Hessian and stationary point; its proof needs no change.
- **Local minimum and boundary rate, Section 7.** The cubic witness has a
  strict local minimum, and is unbounded below when rho>0. The local theorem's
  introductory class now says local minimizer. The explanatory effective
  condition number is restricted to delta<mu; at delta=mu its denominator
  vanishes and the exact terminal factor is one. The numbered nonexpansion
  theorem correctly retains delta<=mu.
- **Normalized limit profile, Remark 7.1.** The vanishing statement concerns
  the limiting normalized profile. The actual first diagonal grows like
  log(N), so it was not literally correct to say that the unnormalized finite
  profile vanishes at early times. The normalization is now explicit.
- **Consensus target, Corollary 8.1(b).** The statement now specifies
  x*=bar(x_0)1 and 0<=p<1. Preservation of the average alone does not make
  x_s-x* mean zero for an arbitrary stationary x*. The proof already used this
  target; the graph/frame and finite-gossip interfaces remain unchanged.

The fresh checks confirmed the numbered conclusions, the actual operator-norm
bound, finite positive converse, genuine recorded-CG construction, signed
arbitrary-memory lower bound, positive-fibre Schur statement, reversal and
stationarity, all-block sine estimates, normalized Lp limits, local confinement,
full-vector Taylor expansion, general quadratic covariance, finite original-space
noise models, varying-law gossip, exact accuracy ceilings and actual nonlinear
algorithms. At N=2 the sine and prefix methods coincide with d=(2,2), which the
current flatness and asymptotic-comparison statements correctly permit.

No mathematical Lean source, root import or showcase signature changed in this
recheck. The strict offline completeness check passes with the same 34 numbered
rows, 19 prose groups, 413 references and 5815 owned declarations. Independent
kernel replay and the tooling/downstream tests reported below remain validations
of these unchanged proof/tool sources; they were not rerun as new semantic tests.
The corrected manuscript and supplementary were rebuilt, with the merged PDF
remaining 24 pages. No automatic TeX/PDF comparison was used.

## Further adversarial review and explicit nonlinear translation

A further independent read of the active statements and written appendix proofs
found one new unsupported prose implication in Section 8: perturbations scaling
with the current error need not be largest at the start of a sampled gossip run.
For a two-vertex unit-weight graph, calibration [1,3], p=3/4 and an active edge,
the first error is -3 e_0; if that edge is active again, the next oracle
perturbation has three times the first norm. The exact mean/variance and
small-p statements are unaffected. The introduction now explains only the unperturbed residual weights in the
leading term. The following comparison is explicitly limited to first-step
transmission at the slowest output mode, rather than ranking an arbitrary full
noise process from its first-step coefficient.

The origin-centered nonlinear estimates already permit the standard coordinate
change e=x-a. This review made that transport an explicit public proof:

- [Two-term translation](TwoTerm/Translation.lean) proves equality of the actual
  physical recurrence minus a with the translated-oracle run. It assumes
  fixed-point coefficients only for 0<s<N; the canonical first step and N=0/1
  need no further condition. Stationarity is not required for this identity.
- The same module proves unconditional gradient, actual Hessian and actual
  third-gradient-derivative transport. Original first/second derivative germs
  near a and third differentiability at a imply the centered regularity record.
- [Nonlinear translation](Nonlinear/Translation.lean) derives fixed-point
  conditions for both method families, constructs Hessian control from
  primitive data on the original ball centered at a, and proves confinement,
  terminal and weighted second-order estimates for the literal physical run.
  The C_N coefficient and exponential factor are unchanged.
- The full-vector expansion at a uses the original objective's derivative
  hypotheses at a, its actual Hessian in the conclusion, and the transported
  actual third tensor. No trajectory bound or desired expansion is assumed.

Two independent semantic reviews inspected these interfaces in addition to the
compiler/kernel checks. The remaining numbered statements, finite probability
models and written proof steps were rechecked without new findings. In
particular, the Rogers trigonometric cancellation, terminal Fourier modes,
continuant coefficient extraction, half-mesh bounds, singular-ODE uniqueness,
moving indices, exact accuracy ceilings and algorithm executions were inspected
inside their proof bodies.

All pre-existing mathematical Lean files retain their exact contents. This
revision adds two modules and updates only the public imports and signature
showcase among existing Lean files. The current inventory has 34 numbered rows,
19 prose groups and 424 signature references.

## Earlier extensions and compatibility

The earlier G1–G7 additions remain proved: full finite-horizon Jacobi converse,
mean-zero spherical gossip reversal, actual pointwise-third full-vector expansion
and sharp Z bound, primitive-sample matrix/gossip models, general PSD quadratic
covariance, prefix-profile monotonicity, and background Favard/CG/Schur/numerical
results. Existing W1–W6 corrections are retained: necessary flatness without an
unproved nonattainment claim, exact Chebyshev versus cosh bounds, terminal versus
difference amplification, valid restart domains, final-exact first-step
transmission and fixed-point premises in the positive converse.

These obligations had different origins. Some strengthened the new manuscript;
others completed old surrounding/background claims that the original signature
inventory had not proved. The old numbered forward construction, conditional
trajectory-radius result and deterministic reversal were not the missing iff,
full-vector Taylor or stochastic-reversal theorems. No old mathematical theorem
was removed, weakened or presented as having failed.

Hash comparison with both the original-extension and current-repair snapshots
confirms that all pre-existing mathematical Lean modules retain their exact
contents. Changes to existing package Lean files are confined to the public root
imports and Article showcase. The repairs add 21 mathematical modules;
the complete extension comprises 111 modules. Existing names, declaration types
and granular import paths are preserved.

## Final validation

- The current strict offline package check passes: 34 numbered rows, 19 prose
  groups, 424 signature references, 267 imported sources including the root,
  5836 owned declarations and all 4120 Lake jobs current. Used mathematical
  axioms are exactly propext, Classical.choice and Quot.sound. The isolated
  unsafe certificate-witness proposer is outside the mathematical proofs.
- Independent stock-kernel replay passes for the union of all 111 extension
  modules: 2051 artifact declarations, checked against a baseline excluding
  those modules. This includes both new nonlinear translation modules. The full
  package, including original numerical certificates, passes the ordinary
  kernel build and declaration/axiom audit above.
- All 21 article-inventory tests pass again. The 91 verification/typesetting
  tooling tests passed before this extension; the shared tooling sources have
  not changed since. Source/inventory checks and Lake verification targets pass
  for chebyshev2, jacobi, krylov, bezout, polyak and nesterov.
- The corrected article and supplementary compile and merge into the root PDF,
  still 24 pages. Source hashes, formatting and inventory consistency checks pass.
