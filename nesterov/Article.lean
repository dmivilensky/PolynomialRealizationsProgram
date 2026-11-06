import nesterov

/-!
Exact (Non-)Accelerations of Heavy-Ball Discretizations: ordered source inventory.
All numbered source statements are checked by their actual signatures.
The semantic review also covers labelled formulas and supporting mathematics.
The full-package audit checks every owned declaration.
See ArticleMap.md for the same ordered references and supporting obligations.
-/

/-!
Article: Lemma 2.1 [lem:qstab].

Exact quadratic-root criterion for 0<μ<L, h>0, 0≤β<1, τ≥0. Stable means every curvature/root is inside the unit disk; the literal maximum is proved attained. Parameter-domain assumptions are separate from stability.
-/
#check @nesterov.Momentum.Tuning
#check @nesterov.Quadratic.stable_iff
#check @nesterov.Quadratic.quadraticRate_lt_one_iff

/-!
Article: Definition 2.2 [def:rate].

Literal all-Hilbert free-state ratios and suprema; actual centered objectives with genuine gradients. All restart times give the same ratio set. The positive-horizon root limit defines the uniform rate; rest suprema use finite dimension and constant initial memory. Universe-polymorphic Euclidean compression validates every real Hilbert carrier. The τ=0 rest quantities equal the existing Polyak quantities exactly.
-/
#check @nesterov.Rates.HilbertRun
#check @nesterov.Rates.ratios
#check @nesterov.Rates.envelope
#check @nesterov.Rates.rate
#check @nesterov.Rates.restRatios
#check @nesterov.Rates.restEnvelope
#check @nesterov.Rates.restRate
#check @nesterov.Rates.quadraticRate
#check @nesterov.Rates.quadraticRate_isGreatest
#check @nesterov.Momentum.momentumRate
#check @nesterov.Momentum.restEnvelope_heavyBall
#check @nesterov.Momentum.restRate_heavyBall
#check @nesterov.Momentum.normalized_objective_iff
#check @nesterov.Momentum.centered_normalized_objective_iff
#check @nesterov.Momentum.momentumRate_normalized
#check @nesterov.Momentum.momentumRestRate_normalized
#check @nesterov.Momentum.queryRestRate_normalized
#check @nesterov.Momentum.quadraticRate_method

/-!
Article: Lemma 2.3 [lem:envelope].

Finite dimension-independent majorant, submultiplicativity, genuine root convergence and infimum over n≥1, scalar quadratic lower bound and rest≤free bound. Zero states are absorbing. Centering at the actual minimizer and all restarts are explicit; no stability/coprimality hypothesis is added.
-/
#check @nesterov.Rates.ratios_eq_restart_ratios
#check @nesterov.Rates.envelope_le
#check @nesterov.Rates.envelope_submultiplicative
#check @nesterov.Rates.tendsto_envelope_root
#check @nesterov.Rates.rate_eq_inf
#check @nesterov.Rates.quadraticRate_le_rate
#check @nesterov.Momentum.quadraticRate_le_momentumRate
#check @nesterov.Rates.restRate_le_rate
#check @nesterov.StationaryMethod.actual_error_stateNorm_le_envelope

/-!
Article: Remark 2.4 [rem:uniform-smoothness]. Uniform rates and smooth subclasses.

Exact finite-horizon supremum equality under finite-dimensional C∞ restriction, with unchanged μ,L and identical initial memory, also from rest. Actual convolution derivative, recentered minimizer error and finite-execution convergence are proved. Euclidean transport preserves smoothness. Literal squared envelopes/rates and doubled first-order constant are included.
-/
#check @nesterov.StationaryMethod.exists_euclidean_prefix
#check @nesterov.Smooth.exists_centered_contDiff_radius
#check @nesterov.Smooth.exists_centered_contDiff_approx
#check @nesterov.Smooth.run_tendsto
#check @nesterov.Rates.smoothEnvelope_eq_envelope
#check @nesterov.Rates.smoothRestEnvelope_eq_restEnvelope
#check @nesterov.Rates.HilbertRun.euclideanObjective_contDiff
#check @nesterov.Rates.tendsto_smoothEnvelope_root
#check @nesterov.Rates.smooth_restRate_eq
#check @nesterov.Rates.squaredEnvelope_eq
#check @nesterov.Rates.tendsto_squaredEnvelope_root
#check @nesterov.Rates.restSquared_root_limsup
#check @nesterov.Rates.squared_first_order_constant

/-!
Article: Lemma 2.5 [lem:cq]. Quadratic constant.

The attained actual quadratic-root maximum has the stated coefficient limsup for every scaling and the exact limit in the strict stable bulk; the filter-polymorphic statement includes nonsmooth families and subsequences.
-/
#check @nesterov.TwoStep.Scaling.quadratic_coefficient_limsup_le
#check @nesterov.TwoStep.Scaling.quadratic_coefficient_tendsto

/-!
Article: Theorem 2.6 [thm:B]. Exact constant.

The lower witness dimension J(theta,y,delta) is fixed before the family, tau and epsilon. One genuine objective and one nonzero rest start work at all horizons, including the real quadratic branch. Beyond the wall, a proved lag-one certificate bounds the actual rate; full and rest coefficients have the same literal kappa limit.
-/
#check @nesterov.TwoStep.common_lower_dimension
#check @nesterov.TwoStep.Scaling.sampled_rest_witness_of_spread
#check @nesterov.TwoStep.Scaling.quadratic_branch_rest_lower
#check @nesterov.TwoStep.Scaling.bulk_lagOne_upper
#check @nesterov.TwoStep.Scaling.bulk_coefficients_tendsto
#check @nesterov.TwoStep.Scaling.bulk_kappa_constants

/-!
Article: Theorem 2.7 [thm:price]. Price of extrapolation.

Exact κτ price bound and iff equality at precisely τ=0 and Polyak beta/step. The bound uses the actual attained quadratic-root maximum and the standing original tuning domain.
-/
#check @nesterov.Quadratic.price_of_extrapolation
#check @nesterov.Quadratic.price_equality_iff_polyak

/-!
Article: Theorem 3.1 [thm:flow]. Exact decay of the heavy-ball flow.

(a) exact weighted Lyapunov derivative, every real c; (a) explicit coercivity constant depending only on θ,m,c; (a) actual state square bound for all t≥0; (b) actual scalar real quadratic solution with literal exponent cQ, all damping regimes; (c) genuine m,L objective on real dimension 2J and actual solution, exact position/velocity norms and all three exponents; (d) all six literal sInf equalities for state/value/energy over F_m and its finite-global-L subclass; (d) endpoint O(exp(-θt/3)) under the exact strict damping condition; literal ordinary logarithmic liminf for every actual nonzero solution; equivalence of nontrivial initial state and source x not identically zero; literal F_m class: differentiability, gradient Lipschitz on bounded sets, convex remainder; unique minimizer in arbitrary Hilbert space, no finite global smoothness assumption; global half-line existence and uniqueness from arbitrary initial x0,v0.
-/
#check @nesterov.Flow.IsSolution.hasDerivAt_weighted_lyapunov
#check @nesterov.Flow.lyapunov_coercive
#check @nesterov.Flow.IsSolution.state_decay
#check @nesterov.Flow.exists_quadratic_witness
#check @nesterov.Flow.exists_real_spiral_witness
#check @nesterov.Flow.exact_worst_exponents
#check @nesterov.Flow.IsSolution.third_rate_bound
#check @nesterov.Flow.IsSolution.decayExponent_eq_article
#check @nesterov.Flow.IsSolution.initial_zero_iff_stationary
#check @nesterov.Flow.stronglyConvexObjective_iff_standard
#check @nesterov.Flow.StronglyConvexObjective.existsUnique_minimizer
#check @nesterov.Flow.exists_unique_solution
#check @nesterov.Flow.Spectrum.radialRatio_eq
#check @nesterov.Flow.Spectrum.secondMoment_ge_scale
#check @nesterov.Flow.profileRatio_tendsto
#check @nesterov.Flow.effectiveDegree_tendsto_one
#check @nesterov.Flow.Spectrum.radialRatio_tendsto
#check @nesterov.Flow.homogeneous_dissipation
#check @nesterov.Flow.le_cF_iff
#check @nesterov.Flow.minimum_step_of_level
#check @nesterov.Flow.homogeneous_degree_ge_one

/-!
Article: Corollary 3.2 [cor:damping]. The price of nonlinearity.

global nonlinear maximum bound sqrt(m/2); unique maximizing damping θ=3sqrt(m/2); quadratic maximum sqrt(m), only at critical damping; equality of cQ and θ/3 at nonlinear optimum; componentwise domination by a point of the exact stated Pareto arc.
-/
#check @nesterov.Flow.cF_le_optimal
#check @nesterov.Flow.cF_eq_optimal_iff
#check @nesterov.Flow.cQ_eq_sqrt_iff
#check @nesterov.Flow.cQ_at_nonlinear_optimal
#check @nesterov.Flow.pareto_domination
#check @nesterov.Flow.cQ_strictMonoOn_underdamped
#check @nesterov.Flow.cQ_strictAntiOn_overdamped
#check @nesterov.Flow.cQ_reciprocal_formula
#check @nesterov.Flow.cF_critical
#check @nesterov.Flow.nonlinear_optimal_rate_ratio
#check @nesterov.Flow.nonlinear_optimal_damping_ratio

/-!
Article: Proposition 3.3 [prop:one]. Single-spiral obstruction.

one common csharp interval excludes every nonnegative atom frequency; explicit first-return upper bound γ≤πc²/(θ-2c); actual F_m solution obstruction in arbitrary Hilbert space with a⊥b and equal positive norms.
-/
#check @nesterov.Flow.exists_oneAtom_obstruction
#check @nesterov.Flow.oneAtom_frequency_upper
#check @nesterov.Flow.no_single_spiral_trajectory

/-!
Article: Lemma 4.1 [lem:norm]. {\cite[Lemma~A.1]{TA}}.

The genuine μ-strongly convex L-smooth class is in exact bijection with the centered normalized class on every real Hilbert space; the existing Polyak normalization is reused literally.
-/
#check @nesterov.Spectral.normalizationEquiv
#check @nesterov.Spectral.normalizeFunction
#check @nesterov.Spectral.denormalizeFunction
#check @nesterov.Spectral.hasGradientAt_normalize
#check @nesterov.Spectral.hasGradientAt_denormalize

/-!
Article: Theorem 4.2 [thm:interp]. {\cite[Theorem~A.2]{TA}}.

Necessary and sufficient interpolation on an arbitrary index set containing the zero datum, with actual globally differentiable normalized functions and exact values and gradients. Neither boundedness nor finite cardinality is assumed.
-/
#check @nesterov.Spectral.hilbert_interpolation_iff
#check @nesterov.Spectral.datumT
#check @nesterov.Spectral.datumR

/-!
Article: Definition 4.3 [def:slm].

Actual D-memory causal scalar stationary methods with u(1)=1, v(1)=0, degree restrictions and nonzero leading coefficient. Coefficient/polynomial formulations, real queries, state norms, unique full execution and source characteristic roots are proved equivalent. Common roots and unstable methods remain allowed.
-/
#check @nesterov.StationaryMethod
#check @nesterov.StationaryMethod.query
#check @nesterov.StationaryMethod.IsTrajectory
#check @nesterov.StationaryMethod.stateNorm
#check @nesterov.StationaryMethod.run
#check @nesterov.StationaryMethod.run_isTrajectory
#check @nesterov.StationaryMethod.IsTrajectory.unique
#check @nesterov.StationaryMethod.queryPolynomial_one
#check @nesterov.StationaryMethod.recurrencePolynomial_one
#check @nesterov.StationaryMethod.queryPolynomial_natDegree_lt
#check @nesterov.StationaryMethod.recurrencePolynomial_natDegree
#check @nesterov.StationaryMethod.source_characteristic_root_iff

/-!
Article: Remark 4.4 [rem:twostep]. Two-step methods.

Full algebraic two-step classification, exact actual gradient-correction state bijection and uniform rate equality under β≠τ/(1+τ); source query inverse filter and both from-rest rate inequalities retain the pole τ/(1+τ). QHM has its own accumulator executor with d₋₁=0 and literal iterate-ratio/envelope/rate dictionaries. Eventual accelerated-family specialization also uses later asymptotic bounds; all finite-tuning dictionaries and the exact pole criterion are proved here.
-/
#check @nesterov.Momentum.two_step_coefficients
#check @nesterov.Momentum.history_isTrajectory
#check @nesterov.Momentum.queryIterate_recurrence
#check @nesterov.Momentum.gradientCorrection_parameters
#check @nesterov.Momentum.Correction.stateEquiv
#check @nesterov.Momentum.Correction.IsTrajectory.existsUnique_query_history
#check @nesterov.Momentum.Correction.determinant_ne_zero_iff
#check @nesterov.Momentum.Correction.rate_eq_momentumRate
#check @nesterov.Momentum.iterate_query_inverse_formula
#check @nesterov.Momentum.queryRestRate
#check @nesterov.Momentum.query_rest_rate_sandwich
#check @nesterov.Momentum.queryRestRate_eq_restRate_of_pole_lt_rest
#check @nesterov.Momentum.qhmIterate_eq_queries
#check @nesterov.Momentum.qhm_parameters_admissible
#check @nesterov.Momentum.qhmExtrapolation_one
#check @nesterov.Momentum.qhmExtrapolation_self
#check @nesterov.Momentum.qhmRatios_eq_queryRestRatios
#check @nesterov.Momentum.qhmEnvelope_eq_queryRestEnvelope
#check @nesterov.Momentum.qhmRate_eq_queryRestRate
#check @nesterov.Momentum.eventually_queryRate_eq_of_rest_tendsto_one
#check @nesterov.Momentum.eventually_queryRate_eq_of_query_tendsto_one

/-!
Article: Definition 4.5 [def:feas].

The division-free pair u,p retains query zeros and common modes. One probability measure and one common value constant satisfy both minimizer bounds and both inequalities at every positive integer lag. The lower and upper slacks are literal; an active lag is positive and has at least one zero slack.
-/
#check @nesterov.Spectral.SymbolPair
#check @nesterov.Spectral.Feasible
#check @nesterov.Attainment.lowerSlack
#check @nesterov.Attainment.upperSlack
#check @nesterov.Attainment.activeLags

/-!
Article: Definition 4.6 [def:cert].

Finite positive-lag support, nonnegative weights, exact cancellation of the common value constant and a strictly negative frequency symbol on the whole compact frequency interval.
-/
#check @nesterov.Duality.StrictCertificate

/-!
Article: Theorem 4.7 [thm:A]. Spectral closure.

All five clauses use the actual stationary executor and literal uniform rate. The exponent set has a greatest element; strict finite certificates characterize rates above it, and one exponent suffices above the middle quadratic radius. Every feasible measure gives one genuine objective and an orthogonal self-similar state trajectory. Atomic L² spaces have literal real Euclidean coordinates. Boundary attainment includes the quadratic case, strict minimizer slack, finite active lags, one common finite carrier for every optimal pair, and the half-degree atom bound from the largest active lag of any fixed optimal pair. The nonquadratic finite-attainment clause additionally requires T>log(rho_q) and T≠0; no coprimality hypothesis is needed.
-/
#check @nesterov.Closure.isClosed_spectralSet
#check @nesterov.Closure.bddAbove_spectralSet
#check @nesterov.Closure.T_isGreatest
#check @nesterov.Closure.log_quadraticRate_le_T
#check @nesterov.Closure.rate_eq_exp_T
#check @nesterov.Closure.certificate_above_T
#check @nesterov.Closure.no_certificate_of_feasible
#check @nesterov.IQC.one_exponent
#check @nesterov.Closure.feasible_above_middle_iff
#check @nesterov.Spectral.Feasible.exists_rotating_objective
#check @nesterov.Spectral.stateVector_step
#check @nesterov.Spectral.norm_stateVector
#check @nesterov.Spectral.atomicRealCoordinates
#check @nesterov.Attainment.quadratic_optimal_attainment
#check @nesterov.Attainment.optimal_strict_minimizer
#check @nesterov.Attainment.optimal_activeLags_finite
#check @nesterov.Attainment.atom_count_of_largest_active
#check @nesterov.Attainment.optimal_real_attainment_with_atom_count
#check @nesterov.Attainment.quadratic_optimal_real_attainment
#check @nesterov.Attainment.optimal_activeLags_has_maximum

/-!
Article: Corollary 4.8 [cor:rest]. Worst cases from rest.

One fixed genuine objective in real dimension 2J+1 and one nonzero from-rest start realize every finite feasible spectrum, with a uniform all-horizon exponential lower bound and a vanishing auxiliary scalar coordinate. The literal rest and free-state factors coincide in both stated cases; the quadratic boundary is attained on the real line, and the nonquadratic boundary by one fixed finite-dimensional real objective with the correct trajectory root limsup.
-/
#check @nesterov.Realization.exists_real_startup
#check @nesterov.Realization.exp_le_momentumRestRate_of_feasible
#check @nesterov.Realization.restRate_eq_momentumRate_of_quadratic
#check @nesterov.Realization.exists_quadratic_worst_from_rest
#check @nesterov.Realization.exists_worst_from_rest_above_quadratic

/-!
Article: Proposition 4.9 [prop:lagone]. Lag-one criterion.

All three original complex-circle criteria imply the strict actual uniform-rate bound. The circle of radius r is handled with the source lag-one weights; the punctured unit circle is strictified using balanced minimizer multipliers, including the mixed lag-one/lag-two criterion for every λ≥0.
-/
#check @nesterov.Phase.momentumRate_lt_of_lagOne
#check @nesterov.Phase.momentumRate_lt_one_of_lagOne
#check @nesterov.Phase.momentumRate_lt_one_of_mixed

/-!
Article: Proposition 4.10 [prop:cycles]. Phase locking.

A single actual objective on ℝ³ and one nonzero from-rest start give the all-horizon nonvanishing bound and convergence to an explicit K-periodic planar rational-rotation orbit. A strict phase bound gives the strict inequality ρ_F⁰>1; every integer, coprimality and phase hypothesis is retained.
-/
#check @nesterov.Phase.exists_periodic_startup
#check @nesterov.Phase.one_lt_restRate_of_strict_phase

/-!
Article: Definition 5.1 [def:second]. Second-order families.

Continuous fixed-memory families retain only the source coefficient limits and the distinguished slow root. The factorization and quotient/step limits are proved, and the literal two-step scaling is embedded by an endpoint extension.
-/
#check @nesterov.Slow.SecondOrderFamily
#check @nesterov.Slow.SecondOrderFamily.CoeffCk
#check @nesterov.Slow.SecondOrderFamily.beta_coeff_ck
#check @nesterov.Slow.SecondOrderFamily.quotient_coeff_ck
#check @nesterov.Slow.SecondOrderFamily.factorization
#check @nesterov.Slow.SecondOrderFamily.stepAt_tendsto
#check @nesterov.TwoStep.Scaling.toSecondOrderFamily

/-!
Article: Theorem 5.2 [thm:ceiling]. Ceiling.

The actual all-objective rate satisfies the literal condition-number limsup ceiling, with extended reals allowing unstable fast modes. One spread spectrum and its distinct positive atoms are fixed before epsilon; its actual objective and orthogonal full-memory trajectory live in real dimension 2J.
-/
#check @nesterov.Slow.SecondOrderFamily.kappa_limsup_coefficient_le
#check @nesterov.Slow.sampled_flow_feasible
#check @nesterov.Slow.spread_frequency_injective
#check @nesterov.Slow.sampled_flow_rotating

/-!
Article: Corollary 5.3 [cor:ceiling]. Consequences of the ceiling.

Both actual rate ceilings and componentwise Pareto domination use the stated damping arc. Critical damping, both Nesterov slow-data examples and necessary theta>=3, y>=theta-1>=2 are proved; kappa and epsilon descriptions have equal limsup/liminf.
-/
#check @nesterov.Slow.SecondOrderFamily.kappa_nonlinear_optimal_ceiling
#check @nesterov.Slow.SecondOrderFamily.kappa_pareto_ceiling
#check @nesterov.Slow.SecondOrderFamily.kappa_critical_ceiling
#check @nesterov.Slow.SecondOrderFamily.standard_nesterov_data_ceiling
#check @nesterov.Slow.SecondOrderFamily.quadratic_nesterov_data_ceiling
#check @nesterov.Slow.SecondOrderFamily.kappa_necessary_slow_data

/-!
Article: Lemma 5.4 [lem:low]. Low frequencies of the limit method.

The exact complex cubic and even real quartic jets have analytic remainders of the stated orders. Effective lead is invariant under normalized common factors, equals tau for the two-step method, and gives the source phase ratio. The rational transfer function has the exact local analytic Taylor remainder. The discrete-difference half-step multiplier is a literal complex identity.
-/
#check @nesterov.Faithful.transfer_quotient_expansion
#check @nesterov.Faithful.normalized_transfer_expansion
#check @nesterov.Faithful.effectiveLead_common_factor
#check @nesterov.Faithful.effectiveLead_momentum
#check @nesterov.Faithful.product_expansion
#check @nesterov.Faithful.symbol_expansion
#check @nesterov.Faithful.phase_lead_limit
#check @nesterov.Faithful.half_step_multiplier
#check @nesterov.Faithful.exists_leading_even_term
#check @nesterov.Faithful.leading_even_order_ge_two
#check @nesterov.Faithful.leading_order_two_iff

/-!
Article: Theorem 5.5 [thm:faithful]. Faithful discretization and the half-step rule.

All four clauses concern actual stationary trajectories and rates. The positive-symbol branch retains the original C^(2p) and u0-2v0 root hypotheses (a stronger C1 result is proved). Below-half and negative half-degenerate contacts give growing planar witnesses at every sufficiently large fixed period; negative lead gives a uniformly unstable scalar quadratic. Fast rational resonances retain the nonzero endpoint-product hypothesis.
-/
#check @nesterov.Faithful.faithful_source
#check @nesterov.Faithful.faithful_rate_linear
#check @nesterov.Faithful.family_below_half
#check @nesterov.Faithful.family_half_negative
#check @nesterov.Faithful.negative_lead_divergence
#check @nesterov.Faithful.negative_lead_planar
#check @nesterov.Faithful.negative_lead_kappa_liminf
#check @nesterov.Faithful.limit_pair_nonzero
#check @nesterov.Faithful.fast_resonance

/-!
Article: Corollary 5.6 [cor:lead]. Necessary lead.

Necessary lead follows from genuine quadratic and nonlinear stability. The exact negative-lead obstruction is a fixed scalar quadratic with an unbounded real trajectory, rather than an assumed unstable limiting mode.
-/
#check @nesterov.Faithful.necessary_lead_quadratic
#check @nesterov.Faithful.necessary_lead
#check @nesterov.Faithful.stable_symbol_eventually_nonnegative

/-!
Article: Remark 5.7 [rem:halfstep]. Extremal leads.

The standard Nesterov limit has phase omega on the closed upper arc. The TMM limit has phase omega/2 wherever its endpoint product is nonzero, namely 0<omega<pi; at pi that product vanishes and the phase is undefined. Its zero-symbol identity still holds at every frequency. The slow lag-one symbol has the opposite minimizer slack and its exact positivity criterion.
-/
#check @nesterov.Faithful.nesterov_angle
#check @nesterov.Faithful.tmm_angle
#check @nesterov.Trace.DoubleRootData.tmmTransfer_zero_symbol
#check @nesterov.Faithful.slow_symbol_opposite_slack
#check @nesterov.Faithful.slow_symbol_positive_iff
#check @nesterov.Faithful.solid_curve_contacts
#check @nesterov.Faithful.solid_curve_contact_iff
#check @nesterov.Faithful.tmm_product_at_pi
#check @nesterov.Faithful.tmm_symbol_zero

/-!
Article: Theorem 5.8 [thm:trace]. Trace formula.

Both source parts are proved. The exact trace integral is integrable and bounded, including the canceled optional simple root at -1. Zero symbol is equivalent to the TMM transfer identity. Under the original closed-disk pencil and nonnegative-symbol hypotheses, common factors are removed and y<=2 with equality exactly at that transfer; no strict root or coprimality assumption is added. The low-frequency integrand limit is literal. Exterior-real quotient bounds give the endpoint squeeze and rigidity.
-/
#check @nesterov.Trace.DoubleRootData.curvature_trace_formula_of_closed
#check @nesterov.Trace.DoubleRootData.trace_formula
#check @nesterov.Trace.DoubleRootData.traceIntegrand_integrable
#check @nesterov.Trace.DoubleRootData.traceIntegrand_bounded
#check @nesterov.Trace.DoubleRootData.zero_symbol_iff_tmmTransfer
#check @nesterov.Trace.DoubleRootData.exterior_fraction_bounds
#check @nesterov.Trace.DoubleRootData.trace_bound_rigid
#check @nesterov.Trace.DoubleRootData.tmmTransfer_iff_cross_identity
#check @nesterov.Faithful.trace_integrand_limit

/-!
Article: Corollary 5.9 [cor:yle2]. The price of a faithful lead.

Eventual actual quadratic stability implies the closed limiting pencil. A nonnegative limit symbol gives y<=2 and the stated full/quadratic kappa ceilings; constant at least one forces theta=3, y=2, the exact TMM transfer, lead one-half and identically zero symbol. Strict faithful discretization has y<2 and constant below one.
-/
#check @nesterov.Faithful.closed_limit_pencil
#check @nesterov.Faithful.faithful_price_kappa_ceilings
#check @nesterov.Faithful.optimal_kappa_transfer_rigidity
#check @nesterov.Faithful.strict_faithful_step

/-!
Article: Proposition 6.1 [prop:Ltau]. Lag-one polynomial.

The exact lag-one quadratic, source coefficients and both stable endpoint signs are proved. All three principal-phase sign equivalences include omega=pi; positivity gives the actual full-class rate below one. The limit-method symbol has exactly the stated strict/weak positivity regions and implies the literal u0-2v0 root condition.
-/
#check @nesterov.TwoStep.physical_lagOne_polynomial
#check @nesterov.TwoStep.Ltau_zero_pos
#check @nesterov.TwoStep.stable_Ltau_two_pos
#check @nesterov.TwoStep.stable_Ltau_phase_sign
#check @nesterov.TwoStep.positive_Ltau_rate
#check @nesterov.TwoStep.limitData_lead
#check @nesterov.TwoStep.limitData_symbol
#check @nesterov.TwoStep.limit_method_positive_iff
#check @nesterov.TwoStep.limit_method_nonnegative_iff
#check @nesterov.TwoStep.limit_middle_roots_lt
#check @nesterov.TwoStep.half_wall_symbol

/-!
Article: Theorem 6.2 [thm:wall]. The wall \(\tau=\tfrac12\).

The original limsup-below-half hypothesis gives, for every sufficiently late actual accelerated tuning, a period K>=6 with the strict principal-phase inequality at that same period, one genuine real three-dimensional objective and rest trajectory approaching a K-periodic orbit, and rest rate strictly above one. The resulting liminf half-step rule holds for arbitrary countably generated parameter filters, including real epsilon and kappa families.
-/
#check @nesterov.TwoStep.wall_phase_periodic_rest_filter
#check @nesterov.TwoStep.wall_of_limsup_filter
#check @nesterov.TwoStep.half_le_liminf_tau_filter
#check @nesterov.TwoStep.wall_periodic_rest

/-!
Article: Proposition 6.3 [prop:onedisc]. Single-slow-frequency obstruction.

One csharp is chosen before every bounded slow-frequency band. One epsilon neighborhood then excludes every c in (theta/3,csharp], every nonnegative frequency in that band and every common value charge, for the literal actual singleton spectrum. The proof derives limiting flow feasibility from the first lag and all sampled integer lags; it works for every continuous fixed-memory second-order family.
-/
#check @nesterov.TwoStep.one_slow_frequency_is_not_enough
#check @nesterov.TwoStep.singleProgram_limit_charge
#check @nesterov.TwoStep.singleProgram_limit_flow
#check @nesterov.TwoStep.no_one_slow_frequency

/-!
Article: Proposition 6.4 [prop:boundary]. On the stability boundary.

Both finite and infinite scaled margins give proved lag-one upper bounds and the exact minimum of the flow and alternating constants for actual full/rest rates. The actual quadratic maximum has the corresponding minimum with cQ; the scalar rest trajectory realizes the alternating contribution. The exact margin criterion gives both limiting stability signs, and at the stable zero-margin edge both actual factors converge strictly while their epsilon/kappa acceleration coefficients tend to zero.
-/
#check @nesterov.TwoStep.Scaling.stable_iff_scaled_margin
#check @nesterov.TwoStep.Scaling.eventually_stable_of_margin_limit
#check @nesterov.TwoStep.Scaling.eventually_unstable_of_margin_limit
#check @nesterov.TwoStep.Scaling.eventually_stable_of_margin_atTop
#check @nesterov.TwoStep.Scaling.zero_margin_filter
#check @nesterov.TwoStep.Scaling.zero_margin_coefficients_tendsto
#check @nesterov.TwoStep.Scaling.zero_margin_kappa_tendsto
#check @nesterov.TwoStep.Scaling.boundary_lagOne_upper
#check @nesterov.TwoStep.Scaling.boundary_lagOne_upper_infinite
#check @nesterov.TwoStep.Scaling.boundary_coefficients_tendsto
#check @nesterov.TwoStep.Scaling.boundary_coefficients_tendsto_infinite
#check @nesterov.TwoStep.Scaling.alternating_rate_lower

/-!
Article: Theorem 6.5 [thm:layer]. The boundary layer.

Every source clause concerns actual rates and genuine from-rest witnesses. The lag-one upper bound covers every c below the layer constant, including A tending to minus infinity. Every c above Lambda-positive/3 has one finite-dimensional objective and rest start before all horizons. The original extended-real liminf-above-threshold hypothesis gives a strict same-period phase inequality, a real three-dimensional periodic startup witness and rest-rate growth. Full/rest epsilon and literal kappa limits match, and acceleration is equivalent to the extended-real limsup of the deficit lying strictly below Astar, with no boundedness or convergence assumption on that deficit. Exact plateau, double-root, sixth-order-symbol, frequency/period scales and figure consequences are included.
-/
#check @nesterov.Layer.Astar
#check @nesterov.Layer.Lambda
#check @nesterov.Layer.constant
#check @nesterov.TwoStep.Scaling.layer_upper
#check @nesterov.TwoStep.Scaling.layer_upper_atBot
#check @nesterov.TwoStep.Scaling.layer_lower
#check @nesterov.TwoStep.Scaling.layer_divergence_finite
#check @nesterov.TwoStep.Scaling.layer_divergence_atTop
#check @nesterov.TwoStep.Scaling.layer_divergence_of_liminf
#check @nesterov.TwoStep.Scaling.layer_coefficients_tendsto
#check @nesterov.TwoStep.Scaling.layer_kappa_coefficients_tendsto
#check @nesterov.TwoStep.Scaling.layer_coefficients_tendsto_atBot
#check @nesterov.TwoStep.Scaling.layer_kappa_coefficients_tendsto_atBot
#check @nesterov.TwoStep.Scaling.not_layerAccelerated_of_deficit_limit
#check @nesterov.TwoStep.Scaling.not_layerAccelerated_of_deficit_atTop
#check @nesterov.TwoStep.Scaling.layer_acceleration_iff_explicit
#check @nesterov.Layer.constant_eq_flow_iff
#check @nesterov.Layer.polynomial_minimum_on_nonneg
#check @nesterov.Layer.polynomial_threshold_square
#check @nesterov.Layer.Lambda_s6
#check @nesterov.Layer.Astar_s6
#check @nesterov.Layer.figure_solid_domain
#check @nesterov.Layer.sixth_order_symbol_exact
#check @nesterov.Layer.sixth_order_symbol_limit
#check @nesterov.TwoStep.Scaling.layer_symbol_quotient_uniform
#check @nesterov.TwoStep.Scaling.layer_cubic_uniform
#check @nesterov.Layer.kappa_deficit_identity
#check @nesterov.Layer.rationalPeriod_kappa
#check @nesterov.Layer.rationalAngle_kappa
#check @nesterov.Layer.rationalXi_kappa

/-!
Article: Corollary 6.6 [cor:B]. Known tunings.

All five known-tuning clauses are proved for actual rates and executors. Standard Nesterov has full/rest kappa constant 2/3 and squared-distance constant 4/3. Quadratic-optimal Nesterov has the exact finite-kappa optimal quadratic factor, the source margin and full/rest constant 4/(3*sqrt(3)). QHM necessity derives away the degenerate gradient-descent case, proves the O(epsilon) weight restriction and literal half-step liminf, and its strict-bulk constant concerns the actual usual initialization. Over-relaxed heavy ball has the literal source gradient-correction update, normalized physical parameters and actual correction-rate constant 2/3. HNAG++ has a literal auxiliary-state equivalence, objective-independent norm comparisons and the actual gradient-correction executor. Its full-class kappa coefficient is 2*sqrt(2)/3, its squared coefficient is 4*sqrt(2)/3 and its quadratic coefficient is sqrt(2). Its corner coordinates are theta=2*sqrt(2), a=sqrt(2)/4, b=3*sqrt(2); the initial physical memories are arbitrary.
-/
#check @nesterov.TwoStep.KnownTunings.standard_parameters
#check @nesterov.TwoStep.KnownTunings.standard_constants
#check @nesterov.TwoStep.KnownTunings.standard_kappa_rates
#check @nesterov.TwoStep.KnownTunings.standard_squared_kappa_rate
#check @nesterov.TwoStep.KnownTunings.quadraticOptimal_parameters
#check @nesterov.TwoStep.nesterov_quadratic_price_kappa
#check @nesterov.TwoStep.nesterov_quadratic_optimal_rate_kappa
#check @nesterov.TwoStep.KnownTunings.quadraticOptimal_margin_tendsto
#check @nesterov.TwoStep.KnownTunings.quadraticOptimal_constants
#check @nesterov.TwoStep.KnownTunings.quadraticOptimal_kappa_rates
#check @nesterov.TwoStep.KnownTunings.qhm_weight_isBigO
#check @nesterov.TwoStep.KnownTunings.qhm_fixed_weight_no_acceleration
#check @nesterov.TwoStep.KnownTunings.qhm_quadratic_root_limsup_le_rate
#check @nesterov.TwoStep.KnownTunings.qhm_actual_half_le_liminf
#check @nesterov.TwoStep.KnownTunings.qhm_bulk_rate
#check @nesterov.TwoStep.overrelaxed_physical_step
#check @nesterov.TwoStep.KnownTunings.overrelaxed_normalized_parameters
#check @nesterov.TwoStep.KnownTunings.overrelaxed_physical_kappa_rate
#check @nesterov.Momentum.HNAG.queryStateEquiv
#check @nesterov.Momentum.HNAG.queryStateEquiv_norms
#check @nesterov.Momentum.HNAG.eliminate
#check @nesterov.Momentum.HNAG.correction_parameters
#check @nesterov.Momentum.HNAG.plusPlus_parameters
#check @nesterov.TwoStep.HNAG.parameters
#check @nesterov.TwoStep.HNAG.corner_coordinates
#check @nesterov.TwoStep.HNAG.physical_step
#check @nesterov.TwoStep.HNAG.physical_quadratic_kappa_rate
#check @nesterov.TwoStep.HNAG.physical_correction_kappa_rate
#check @nesterov.TwoStep.HNAG.physical_squared_kappa_rate

/-!
Article: Corollary 6.7 [cor:nag-asymptotic-optimal]. Asymptotically optimal Nesterov tuning.

For every literal kappa>=6 the stated Nesterov tuning is stable and its actual full-class rate is strictly below one. The full and from-rest kappa coefficients both converge to sqrt(2/3). No family with tau=beta has a larger constant: the universal extended-real limsup ceiling requires neither parameter convergence nor eventual quadratic stability.
-/
#check @nesterov.TwoStep.KnownTunings.optimalNesterov_finite
#check @nesterov.TwoStep.KnownTunings.classOptimal_parameters
#check @nesterov.TwoStep.KnownTunings.classOptimal_literal_kappa_rates
#check @nesterov.TwoStep.nesterov_full_kappa_limsup

/-!
Article: Corollary 7.1 [cor:TMM]. TMM.

TMM is the literal robust left endpoint, with its exact three rates, physical slow data and strictly positive deficit of the stated second-order accuracy. Its rate and acceleration constant are optimal among all adaptive deterministic first-order policies, including horizon/dimension-dependent nonlinear queries using every previous value and gradient. Genuine finite-horizon hard objectives are constructed; the literal supremum-before-root-limsup lower bound and actual TMM oracle attainment hold for every 0<mu<L. No span or policy homogeneity restriction is imposed. The HNAG+ parameters at alpha=epsilon/(1-epsilon) coincide exactly with this TMM design.
-/
#check @nesterov.Robust.tmmDesign
#check @nesterov.Robust.tmm_design_equality
#check @nesterov.Robust.Design.tmm_step
#check @nesterov.Robust.Design.tmm_deficit
#check @nesterov.Robust.Design.tmm_tau_lt_half
#check @nesterov.Robust.tmm_exact_rates
#check @nesterov.Robust.tmm_kappa_parameters
#check @nesterov.Robust.tmm_kappa_deficit_isBigO
#check @nesterov.Oracle.Policy
#check @nesterov.Oracle.literalRateAt
#check @nesterov.Oracle.Geometric.finite_hard_scaled
#check @nesterov.Oracle.first_order_literal_rate_lower_at
#check @nesterov.Oracle.tmm_oracle_rate_at
#check @nesterov.Oracle.tmm_oracle_optimal_at
#check @nesterov.Oracle.all_family_kappa_limsup_le_one
#check @nesterov.Oracle.tmm_kappa_coefficient
#check @nesterov.Momentum.HNAG.plus_parameters
#check @nesterov.Momentum.HNAG.plus_eq_tmm

/-!
Article: Theorem 7.2 [thm:corner]. The corner.

All four clauses for the actual method: strict lag-one upper and from-rest lower bounds, literal condition-number liminf/limsup bounds, every stated sufficient condition for matching constants, and the exact optimal wedge. The frequency lower bounds use genuine finite-dimensional objectives and starts fixed before all horizons. Both upper limiting coefficients are bounded without a positive lag-one minimum; outside the optimal wedge they are strictly below one.
-/
#check @nesterov.TwoStep.Scaling.corner_lagOne_upper
#check @nesterov.TwoStep.Scaling.corner_rest_lower
#check @nesterov.TwoStep.Scaling.corner_coefficient_limsup_upper
#check @nesterov.TwoStep.Scaling.corner_kappa_bounds
#check @nesterov.TwoStep.Scaling.corner_kappa_constants
#check @nesterov.TwoStep.Scaling.corner_coefficients_of_discrete_min
#check @nesterov.TwoStep.Scaling.corner_coefficients_of_quadratic
#check @nesterov.TwoStep.Scaling.corner_coefficients_of_polynomial
#check @nesterov.TwoStep.Scaling.corner_coefficients_of_concave
#check @nesterov.TwoStep.Scaling.corner_optimal_iff
#check @nesterov.TwoStep.Scaling.corner_suboptimal_limsup_lt_one
#check @nesterov.TwoStep.Scaling.corner_rest_optimal_of_wedge
#check @nesterov.TwoStep.Scaling.corner_frequency_rest_witness
#check @nesterov.Corner.HalfStepCone
#check @nesterov.Corner.halfStepCone_dirac_iff
#check @nesterov.Corner.not_halfStepCone_of_gap
#check @nesterov.Corner.halfStep_cos_gap_negative
#check @nesterov.Corner.halfStep_lag_lower
#check @nesterov.Corner.halfStep_lag_upper
#check @nesterov.Corner.halfStep_feasible_iff
#check @nesterov.Corner.halfStep_exists_charge_iff

/-!
Article: Remark 7.3 [rem:regions]. Explicit regions.

Both explicit regions give the actual full and from-rest limits with the original inequalities; the polynomial identities establish the signs on the entire frequency interval.
-/
#check @nesterov.Corner.cQ_ge_third
#check @nesterov.Corner.flow_difference
#check @nesterov.Corner.alternating_difference
#check @nesterov.TwoStep.Scaling.corner_flow_region
#check @nesterov.TwoStep.Scaling.corner_alternating_region

/-!
Article: Corollary 7.4 [cor:arc]. The arc at \(\tau=\frac12\).

Explicit physical families attain every point of the half-step arc, with literal condition-number limits for the full, from-rest and quadratic rates. In particular the maximal quadratic constant sqrt(2) is attained.
-/
#check @nesterov.TwoStep.cornerFamily
#check @nesterov.TwoStep.cornerFamily_parameters
#check @nesterov.TwoStep.cornerFamily_coordinates
#check @nesterov.TwoStep.arc_family_coefficients
#check @nesterov.TwoStep.arc_family_kappa
#check @nesterov.TwoStep.maximal_quadratic_corner_kappa

/-!
Article: Theorem 7.5 [thm:optimal]. Optimal tunings of \(\cM\).

The iff applies to arbitrary stable physical tuning families, without assuming parameter convergence. It forces convergence to (3,2,1/2), then characterizes optimality by the attained moving lag-one minimum. The equivalent extended-real liminf and vanishing ratio conditions impose no boundedness on alpha or the margin; the denominator is proved positive. The from-rest condition-number coefficient also tends to one. A bounded nonvanishing defect ratio is excluded by compactness and the proved corner optimality criterion.
-/
#check @nesterov.TwoStep.optimal_tuning_kappa_iff
#check @nesterov.TwoStep.optimal_tuning_kappa_ratio_iff
#check @nesterov.TwoStep.optimal_tuning_kappa_rest_limit
#check @nesterov.TwoStep.optimal_tuning_family_iff
#check @nesterov.TwoStep.optimal_tuning_ratio_reformulation
#check @nesterov.TwoStep.optimal_tuning_family_ratio_iff
#check @nesterov.TwoStep.Scaling.corner_denominator_pos
#check @nesterov.TwoStep.Scaling.corner_margin_coordinates_exact
#check @nesterov.TwoStep.Scaling.optimal_beyond_corner
#check @nesterov.TwoStep.Scaling.corner_no_bounded_defect_bad_sequence

/-!
Article: Theorem 8.1 [thm:tonguefree]. Tongue-free extrapolations.

All three sharp necessity/sufficiency clauses hold over every stable tuning and condition number. The exact lag-two weight repairs the region between tauThree and tauStar. Below the lower threshold one stable tuning gives an actual 3-periodic real startup witness and strict growth from rest. Both radical heavy-ball thresholds and Nesterov/half-step consequences are exact. Between the thresholds a negative symbol is confined to the literal open frequency interval (2*pi/3,pi); the heavy-ball lag-two gap and both threshold limits are explicit.
-/
#check @nesterov.FiniteCondition.lagOne_pos_up_to_three_halves
#check @nesterov.FiniteCondition.stable_lagOne_pos_up_to_three_halves
#check @nesterov.FiniteCondition.negative_lagOne_frequency
#check @nesterov.FiniteCondition.heavyBall_lagTwo_gap
#check @nesterov.FiniteCondition.thresholds_tendsto_wall
#check @nesterov.FiniteCondition.tonguefree_multiplier
#check @nesterov.FiniteCondition.all_stable_converge_iff
#check @nesterov.FiniteCondition.all_stable_lagOne_iff
#check @nesterov.FiniteCondition.three_periodic_witness
#check @nesterov.FiniteCondition.heavyBall_all_stable_iff
#check @nesterov.FiniteCondition.heavyBall_all_stable_lagOne_iff
#check @nesterov.FiniteCondition.half_step_converges
#check @nesterov.FiniteCondition.nesterov_converges
#check @nesterov.FiniteCondition.tauThree_corner_expansion
#check @nesterov.FiniteCondition.tauStar_corner_expansion

/-!
Article: Corollary 8.2 [cor:QHM]. Quasi-hyperbolic momentum.

The exact finite-condition threshold for usual-initialization QHM is equivalent to the source threshold after the proved physical translation, including beta=0.
-/
#check @nesterov.FiniteCondition.qhm_tonguefree_iff

/-!
Article: Proposition 8.3 [prop:mono]. Monotonicity in the condition number.

Inclusion of the original smooth strongly convex classes makes the actual all-objective rate antitone in mu. Finite strict certificates persist as mu varies; under the given largest-curvature stability margin the convergence domain is nonempty and equals one open interval with endpoint in [0,L). Every positive lag-one polynomial lies in that domain.
-/
#check @nesterov.Rates.class_weaken
#check @nesterov.Rates.rate_antitone_mu
#check @nesterov.FiniteCondition.convergenceSet_isOpen
#check @nesterov.FiniteCondition.convergence_interval
#check @nesterov.FiniteCondition.lagOne_interval_near_L
#check @nesterov.TwoStep.positive_Ltau_rate

/-!
Article: Lemma B.1 [lem:cQprop]. The quadratic constant.

(a) exact iff for every real c; (b) positive scaling of cQ; (b) positive scaling of cF.
-/
#check @nesterov.Flow.lt_cQ_iff
#check @nesterov.Flow.cQ_scale
#check @nesterov.Flow.cF_scale

/-!
Article: Lemma B.2 [lem:creduce]. Spirals of the flow.

exact forward time-pair support discrepancy; exact backward time-pair support discrepancy; exact pairwise squared distance; exact minimizer support discrepancy; full iff with one actual finite convex function containing the origin and every real orbit time.
-/
#check @nesterov.Flow.Spectrum.forward_slack
#check @nesterov.Flow.Spectrum.backward_slack
#check @nesterov.Flow.Spectrum.orbit_distance_sq
#check @nesterov.Flow.Spectrum.minimizer_gap
#check @nesterov.Flow.Spectrum.program_iff_convex_interpolant

/-!
Article: Lemma B.3 [lem:extend]. Smooth extension with a margin.

The source margin assumptions, for every real K and any index set containing the zero datum, yield one globally differentiable convex interpolant with exact prescribed values/gradients and gradient Lipschitz constant K²/(2ε). This includes K≤0. Adding the quadratic gives one genuine centered m-strongly convex L-smooth objective for every L>m with L≥m+K²/(2ε), preserving all data.
-/
#check @nesterov.Flow.exists_convex_smooth_interpolant
#check @nesterov.Flow.extend_strict_support
#check @nesterov.Flow.extend_strict_support_real
#check @nesterov.Flow.exists_convex_interpolant_of_margin

/-!
Article: Lemma B.4 [lem:spread]. Spread spectra.

exact equal weights/midpoint frequencies, scale≥1 and one ε∈(0,1] valid for every real q>0, both A+B margins and minimizer gap≥1.
-/
#check @nesterov.Flow.exists_spread
#check @nesterov.Flow.abs_spreadV_le_eight
#check @nesterov.Flow.midpoint_error_secondDerivative
#check @nesterov.Flow.weighted_UV_secondDerivative_bound
#check @nesterov.Flow.midpoint_UV_error_sharp
#check @nesterov.Flow.midpoint_UV_error_uniform_sharp

/-!
Article: Remark B.5 [rem:cone]. The single-spiral cone.

exact iff for literal infimum Upsilon over all positive real lags and minimizer twist inequality; infimum criterion with proved bounded-below and nonempty set.
-/
#check @nesterov.Flow.oneAtom_iff_cone
#check @nesterov.Flow.le_coneProfile_iff

/-!
Article: Lemma C.1 [lem:waves]. Exact spectral interpolation.

Exact planar and real L² interpolation slacks with independent query and gradient amplitudes, including zeros of u. The entire infinite table is realized by one genuine objective and one stationary trajectory. Finite spectra have actual C^J realizations, exact latent exponential norms and real dimension 2J.
-/
#check @nesterov.Spectral.mixture_slack
#check @nesterov.Spectral.mixture_star_slack
#check @nesterov.Spectral.mixtureValue_some
#check @nesterov.Spectral.mixture_interpolation_iff
#check @nesterov.Spectral.Feasible.exists_objective
#check @nesterov.Spectral.Feasible.exists_hilbertRun
#check @nesterov.Spectral.finite_exists_objective
#check @nesterov.Spectral.norm_finiteLatent
#check @nesterov.Spectral.finite_real_dimension

/-!
Article: Lemma C.2 [lem:angle]. Phase of the lag-one symbol.

Both signs of the exact polar defect identity, with the principal phase in (−π,π], are proved. The division-free endpoint factorization connects this phase to the original characteristic symbol. For stable momentum the full half-open upper semicircle has phase in (0,π], including Θ(π)=π.
-/
#check @nesterov.Phase.lag_one_polar_identity
#check @nesterov.Phase.lag_one_phase_identity
#check @nesterov.Phase.polar_representation
#check @nesterov.Phase.stationary_factor
#check @nesterov.Phase.momentumAngle_mem_Ioc
#check @nesterov.Phase.complex_defect_polar
#check @nesterov.Phase.complex_defect_phase
#check @nesterov.Phase.stationary_lag_one_phase_identity
#check @nesterov.Phase.stationary_lag_one_positive_factor

/-!
Article: Lemma C.3 [lem:compact]. Compactness.

Closed feasible graph and compactness over compact moving parameters and continuously varying u,p, including the uniform bound on the common value constant. All infinitely many lag constraints are retained.
-/
#check @nesterov.Spectral.isCompact_feasible_over
#check @nesterov.Spectral.isClosed_feasible

/-!
Article: Lemma C.4 [lem:duality]. Duality.

The full strict alternative: infeasibility is equivalent to existence of a finite strict certificate. Finite-intersection compactness and the finite separation alternative are proved with the common value variable.
-/
#check @nesterov.Duality.infeasible_iff_strictCertificate

/-!
Article: Lemma C.5 [lem:persist]. Strict certificates persist.

Uniform perturbations of g, skew and t preserve the same lag weights and half the strict margin. Both minimizer multipliers receive exactly the positive/negative residual adjustments specified by the article.
-/
#check @nesterov.Duality.StrictCertificate.uniform_gs

/-!
Article: Lemma C.6 [lem:iqc]. Certificate IQC.

On every real Hilbert carrier the Fourier functional is constructed as the unique continuous extension of actual finite-coordinate scalar Fourier integrals, with independence of the common compression and proved all-Hilbert Parseval equality Q=J. It recovers the literal integral on all finite-dimensional signals. The genuine normalized gradient graph, with zero extension, satisfies this IQC (also along the homotopy). The original Hermitian matrix [[A,iB],[−iB,−A]] evaluates on arbitrary complex amplitudes to the exact division-free certificate symbol; actual polynomial amplitudes give Φ.
-/
#check @nesterov.IQC.normalized_gradient_IQC
#check @nesterov.IQC.normalized_gradient_fourier_IQC
#check @nesterov.IQC.certificateMatrix_source
#check @nesterov.IQC.sourceMatrix_quadratic
#check @nesterov.IQC.certificateMatrix_graph
#check @nesterov.IQC.fourierCompression_integral_eq
#check @nesterov.IQC.finiteFourierValue_tendsto
#check @nesterov.IQC.hilbertFourierIQC_eq_time
#check @nesterov.IQC.hilbertFourierIQC_unique
#check @nesterov.IQC.hilbertFourierIQC_eq_integral
#check @nesterov.IQC.normalized_gradient_hilbertFourier_IQC
#check @nesterov.IQC.halfline_hilbertFourier_IQC

/-!
Article: Lemma C.7 [lem:homotopy]. Homotopy.

The source Fourier graph inequality gives one positive gain constant before the spatial dimension, causal nonlinearity and homotopy parameter. Only the prefix gain-from-zero condition is assumed on Δ; incremental Lipschitz continuity is not required. Every square-summable input has a unique actual causal solution, proved square summable by finite-prefix continuation. The scalar convolution has an absolutely summable real impulse response and zero direct term. The gain depends only on this convolution, a uniform matrix bound and the strict graph margin.
-/
#check @nesterov.IQC.homotopy
#check @nesterov.IQC.CausalFeedback.existsUnique_solution
#check @nesterov.IQC.CausalFeedback.iqc_uniform_bound
#check @nesterov.IQC.scalar_bilinearIQC_norm_le
#check @nesterov.IQC.realBilinearIQC_norm_le

/-!
Article: Lemma C.8 [lem:finite]. Finite support.

One probability measure on the two distinct one-point-compactified lag families yields the literal normalized source symbol, its holomorphic extension and strict endpoint negativity. Its finite interior zero set carries every optimal spectrum, and the same dual measure is carried by constraints active for every optimal pair. All infinitely many lags and both minimizer labels remain present.
-/
#check @nesterov.Attainment.exists_boundaryDual
#check @nesterov.Attainment.BoundaryDual.sourceSymbol_eq_integral
#check @nesterov.Attainment.BoundaryDual.sourceSymbol_nonpositive
#check @nesterov.Attainment.BoundaryDual.sourceComplexSymbol_holomorphic
#check @nesterov.Attainment.BoundaryDual.sourceComplexSymbol_physical
#check @nesterov.Attainment.BoundaryDual.sourceSymbol_endpoint_neg
#check @nesterov.Attainment.BoundaryDual.zeroSet_finite
#check @nesterov.Attainment.BoundaryDual.zeroSet_interior
#check @nesterov.Attainment.BoundaryDual.measure_carried
#check @nesterov.Attainment.BoundaryDual.measure_active
#check @nesterov.Attainment.BoundaryDual.sourceZeros_finite
#check @nesterov.Attainment.BoundaryDual.source_measure_carried

/-!
Article: Lemma C.9 [lem:strict]. Strict minimizer slack.

Every optimal pair above the quadratic boundary and with T≠0 has the strict original inequality |C|<ḡ. This follows from the proved finite carrier and oscillatory coefficient argument, without assuming minimizer slack.
-/
#check @nesterov.Attainment.optimal_strict_minimizer

/-!
Article: Lemma C.10 [lem:count]. Atom count.

Every optimal pair has a finite nonempty active-lag set. Choosing the largest active lag N of any one pair gives one common carrier for every other pair, with cardinality at most (D+N)/2. The bound is proved by the degree of the literal dual polynomial and the even multiplicity of its interior zeros, and is used by an actual real Euclidean attaining objective.
-/
#check @nesterov.Attainment.optimal_activeLags_finite
#check @nesterov.Attainment.optimal_activeLags_nonempty
#check @nesterov.Attainment.optimal_activeLags_has_maximum
#check @nesterov.Attainment.atom_count_of_largest_active
#check @nesterov.Attainment.optimal_real_attainment_with_atom_count

/-!
Article: Lemma C.11 [lem:startup]. Start from rest in \(\cM\).

The full actual from-rest executor is the orthogonal sum of the original finite waves shifted by one step and a scalar stable quadratic run tending to zero. One scalar curvature avoids all noninitial returns; one auxiliary amplitude and one globally interpolated objective work for every horizon. Strict minimizer slack is required only for positive exponents. The real dimension is exactly 2J+1.
-/
#check @nesterov.Realization.exists_startup
#check @nesterov.Realization.exists_real_startup

/-!
Article: Lemma C.12 [lem:restquad]. From rest on a quadratic.

For every nonzero real from-rest start, the actual scalar iterate root limsup equals the characteristic root radius. The query limsup has the same value under the exact source nondegeneracy condition. Real, repeated, complex-conjugate and vanishing-root cases are included.
-/
#check @nesterov.Momentum.quadratic_iterate_root_limsup
#check @nesterov.Momentum.quadratic_query_root_limsup

/-!
Article: Lemma C.13 [lem:separate]. Separation of quadratic modes.

A positive lag-one symbol excludes every quadratic root on the specified circle without a prior stability assumption. If the μ-endpoint roots lie strictly inside, all curvatures do; the actual quadratic factor, middle radius and uniform nonlinear factor are strictly below r, and the tuning is stable.
-/
#check @nesterov.Phase.no_root_on_circle_of_lagOne
#check @nesterov.Phase.separate

/-!
Article: Lemma C.14 [lem:single]. One-atom spectra.

The exact rational phase criterion holds for both signs of the principal argument and every positive integer lag. The weak bound produces one feasible atom with C=0 at any exponent where it holds; at t=0 it is also necessary. A strict phase bound persists at a positive exponent, giving a genuine divergent-from-rest witness.
-/
#check @nesterov.Phase.singleton_feasible_of_phase
#check @nesterov.Phase.singleton_feasible_zero_iff_phase
#check @nesterov.Phase.exists_growing_singleton
#check @nesterov.Phase.one_lt_restRate_of_strict_phase

/-!
Article: Proposition C.15 [prop:lyap]. Lyapunov form.

For r in (r_c,1], a proved strict storage/KYP construction chooses one real scalar matrix and one finite value correction before the Hilbert space, objective and trajectory. On the literal state (x_prev−x*,x_cur−x*,σ_k,…,σ_{k+M−1}) the resulting function has positive uniform quadratic comparison and strict r² dissipation. The scalar data and comparison constants may depend on the chosen lag bound M. The actual from-rest iterates obey one uniform K r^N bound. For lag one the correction is exactly the original 4/(L−μ) function-gap expression. No KYP theorem or matrix feasibility is assumed.
-/
#check @nesterov.IQC.KYP.certificateLyapunovData
#check @nesterov.IQC.KYP.LyapunovData.sourceMatrix
#check @nesterov.IQC.KYP.LyapunovData.sourceLyapunov_form_values
#check @nesterov.IQC.KYP.momentumSourceState_original
#check @nesterov.IQC.KYP.LyapunovData.original_source_comparison
#check @nesterov.IQC.KYP.LyapunovData.original_source_step
#check @nesterov.IQC.KYP.LyapunovData.original_iterate_norm_bound
#check @nesterov.IQC.KYP.LyapunovData.original_source_lagOne_form

/-!
Article: Remark C.16 [rem:hill]. Tongues as phase locking of a Hill recursion.

The real symmetric curvature matrix has the exact source entries and operator norm |p̂|≤1. Rational phase gives periodic rotated curvatures and the actual normalized stationary Hill recurrence; the rotating frame is fixed. A scalar contraction exists exactly when Im(p̂)=0, equivalently when the characteristic mode is realized by a curvature λ∈[μ,L].
-/
#check @nesterov.Phase.curvature_matrix_dictionary
#check @nesterov.Phase.curvature_selfAdjoint
#check @nesterov.Phase.curvature_norm
#check @nesterov.Phase.rotatingCurvature_conjugation
#check @nesterov.Phase.rotatingCurvature_periodic
#check @nesterov.Phase.rotating_matrix_phase
#check @nesterov.Phase.feasible_hill_representation
#check @nesterov.Phase.stationary_hill_recursion
#check @nesterov.Phase.rotating_frame_fixed
#check @nesterov.Phase.scalar_contraction_iff
#check @nesterov.Phase.query_ratio_quadratic_iff

/-!
Article: Lemma C.17 [lem:spreadhalf]. Spread spectra at a half step.

The fixed smooth profile is the verified Polyak psi, a permissible once-for-all choice of the source bump. The actual inverse-magnitude-weighted band density has positive mean G, strict minimizer reserve, strict upper slacks for all positive lags and strict lower slacks for lags at least two under the original quantitative phase hypotheses. The original averaged first-lag condition yields feasibility and finite atoms on the same band, preserving every lag and the strict reserve. Polar data need only be continuous on the original band; their continuous extension is proved.
-/
#check @nesterov.Spread.source_bump_properties
#check @nesterov.Spread.source_bump_tsupport
#check @nesterov.Spread.source_kernel_properties
#check @nesterov.Spread.exists_relative_fourier_gap
#check @nesterov.Spread.fourier_margin
#check @nesterov.Spread.lowerSlack_extreme_complex
#check @nesterov.Spread.upperSlack_extreme_complex
#check @nesterov.Spread.lagOneSymbol_complex
#check @nesterov.Spread.lowerSlack_one_extreme
#check @nesterov.Spread.SourceHalfStepData
#check @nesterov.Spread.SourceHalfStepData.noncritical
#check @nesterov.Spread.SourceHalfStepData.feasible_and_finite

/-!
Article: Lemma D.1 [lem:normal]. Slow normal form.

The O(epsilon^3) remainder is uniform on every compact complex slow-coordinate set. Two actual characteristic roots are selected with multiplicity, including critical damping; their exponential coordinates converge to both flow roots. The actual quadratic coefficient has the required one-sided bound.
-/
#check @nesterov.Slow.SecondOrderFamily.normal_form_uniform
#check @nesterov.Slow.SecondOrderFamily.two_slow_roots
#check @nesterov.Slow.SecondOrderFamily.quadratic_coefficient_eventually_le

/-!
Article: Lemma D.2 [lem:split]. Per-atom splitting.

Both per-atom slack identities and the exact absolute-value minimizer equivalence are proved for every positive integer lag and negative exponent.
-/
#check @nesterov.Slow.split_slacks
#check @nesterov.Slow.split_minimizer_iff

/-!
Article: Lemma D.3 [lem:reduce]. Exact reduction and expansion.

For c>0, 0<epsilon<1 and positive step, the homogeneous query-normalization dictionary is an exact iff with the correct reweighted probability vector and charge. Every sampled lag is exactly the flow kernel; both actual normalized coefficients and the query amplitude converge uniformly on compact slow bands.
-/
#check @nesterov.Slow.query_normalization_iff
#check @nesterov.Slow.exists_inverse_query_normalization
#check @nesterov.Slow.sampled_scaled_program_iff
#check @nesterov.Slow.SecondOrderFamily.query_coefficients_exact
#check @nesterov.Slow.SecondOrderFamily.query_wave_uniform
#check @nesterov.Slow.SecondOrderFamily.slowG_uniform
#check @nesterov.Slow.SecondOrderFamily.slowS_uniform

/-!
Article: Lemma D.4 [lem:Cforced]. The value constant is forced.

One constant and one endpoint neighborhood work before every damping in the prescribed compact positive set, every probability measure on the slow band and every feasible charge. The result gives the literal O(epsilon^3) bound and exact slow-integral formula, with a continuous query-normalized extension equal to the true quotient on the entire relevant band.
-/
#check @nesterov.Slow.SecondOrderFamily.value_constant_forced
#check @nesterov.Slow.slow_measure_charge
#check @nesterov.Slow.bandQueryPair_p

/-!
Article: Lemma D.5 [lem:flowspirals]. Sampled flow spirals.

The original fixed flow weights and the exact forced charge satisfy every sampled lag and a strict minimizer reserve. Positive inverse-query reweighting preserves feasibility and the reserve in latent normalization. The grid frequencies are distinct, so the resulting latent spectrum has exactly J positive atoms, fixed before epsilon.
-/
#check @nesterov.Slow.sampled_flow_query_program
#check @nesterov.Slow.sampled_flow_feasible
#check @nesterov.Slow.query_to_latent_feasible
#check @nesterov.Slow.spread_frequency_injective

/-!
Article: Lemma D.6 [lem:twoscale]. Two-scale expansion.

The literal radius 1-c*epsilon has the stated joint cubic expansion with remainder little-o of (epsilon+abs omega)^3, with no restriction on omega/epsilon. The expansion and evenness in omega hold under the baseline continuous-family assumptions; a C3 coefficient germ separately implies C3 regularity of the symbol.
-/
#check @nesterov.Faithful.two_scale_expansion
#check @nesterov.Faithful.linearSymbol_even
#check @nesterov.Faithful.linearSymbol_contDiffWithinAt
#check @nesterov.Faithful.two_scale_at_origin

/-!
Article: Lemma E.1 [lem:cubic]. Lag-one cubic.

The literal product of two monic real quadratics gives the source trigonometric expression, all four exact xi coefficients and both real endpoint values, without stability hypotheses.
-/
#check @nesterov.TwoStep.quad_product
#check @nesterov.TwoStep.lagOne_trigonometric
#check @nesterov.TwoStep.lagOne_cubic
#check @nesterov.TwoStep.lagOne_at_zero
#check @nesterov.TwoStep.lagOne_at_pi

/-!
Article: Lemma E.2 [lem:mixed]. Mixed test.

The exact imaginary cross-characteristic and mixed quadratic identities are proved at arbitrary positive radius. The two sign hypotheses at a rational angle produce an actual feasible singleton with C=0, retaining every integer lag.
-/
#check @nesterov.TwoStep.cross_im_circle
#check @nesterov.TwoStep.mixed_symbol
#check @nesterov.TwoStep.mixedPolynomial_coefficients
#check @nesterov.TwoStep.mixed_test

/-!
Article: Lemma E.3 [lem:band]. Resonance on a band.

The source integer interval contains an admissible period with the full relative-band inclusion. A negative Ltau at the selected rational frequency gives the literal periodic-from-rest real witness and strict rest-rate growth.
-/
#check @nesterov.TwoStep.exists_integer_period_band
#check @nesterov.TwoStep.negative_Ltau_periodic_rest
#check @nesterov.TwoStep.negative_band_restRate
#check @nesterov.TwoStep.resonanceWitness_of_negative

/-!
Article: Lemma E.4 [lem:accel]. Accelerated tunings.

For 0<epsilon<1 and c>0, the exact finite-tuning quantitative bounds are proved for the actual quadratic maximum. A subsequence of the same physical tunings has convergent slow parameters satisfying all source inequalities; no convergence hypothesis is inserted into the compactness conclusion.
-/
#check @nesterov.TwoStep.accelerated_tuning_bounds
#check @nesterov.TwoStep.accelerated_subsequence

/-!
Article: Proposition E.5 [prop:periods]. Range of resonant periods.

The two perturbed real roots give all three source sign intervals. Every admitted integer period has an actual real periodic startup witness. The literal greatest admitted period and the cardinality of the admitted set have the stated common leading asymptotic constant, rather than only order bounds.
-/
#check @nesterov.TwoStep.periodBandEdge_mem
#check @nesterov.TwoStep.period_band_signs
#check @nesterov.TwoStep.resonant_periods_asymptotics
#check @nesterov.TwoStep.period_band_periodic_rest

/-!
Article: Lemma E.6 [lem:Pscaled]. Lag-one and mixed coefficients in the accelerated scaling.

All six lag-one/mixed coefficients have exact polynomial epsilon-squared remainders, and uniform first/second-order estimates on arbitrary compact parameter sets. P0, both characteristic factors, the imaginary bracket and all six corner first derivatives are exact algebraic identities.
-/
#check @nesterov.TwoStep.scaledP0_exact
#check @nesterov.TwoStep.scaled_chiL_exact
#check @nesterov.TwoStep.scaledP1_exact
#check @nesterov.TwoStep.scaledP2_exact
#check @nesterov.TwoStep.scaledP3_exact
#check @nesterov.TwoStep.scaledQ0_exact
#check @nesterov.TwoStep.scaledQ1_exact
#check @nesterov.TwoStep.scaledQ2_exact
#check @nesterov.TwoStep.scaled_cross_im
#check @nesterov.TwoStep.corner_dots
#check @nesterov.TwoStep.uniform_second_order
#check @nesterov.TwoStep.uniform_first_order
#check @nesterov.TwoStep.realCharacteristic_slow

/-!
Article: Lemma E.7 [lem:lagscaled]. Lag-one certificates in the accelerated scaling.

The slow endpoint roots and P0 are strictly inside/positive independently of the fast coefficient premise. Positivity of the stated tail then gives the actual quadratic factor, middle radius and full nonlinear factor strictly below 1-c*epsilon, through the proved lag-one separation theorem.
-/
#check @nesterov.TwoStep.Scaling.slow_endpoint_roots_lt
#check @nesterov.TwoStep.Scaling.P0_eventually_pos
#check @nesterov.TwoStep.Scaling.lag_scaled

/-!
Article: Lemma E.8 [lem:altmode]. The sign-alternating mode.

The actual largest-curvature polynomial has the two stated real roots, the exact rationalized shift and uniform relative remainder. The dominant negative root determines the literal scalar from-rest root limsup and bounds both actual rates. The shift divided by epsilon has the stated finite, zero and infinite limits.
-/
#check @nesterov.TwoStep.alternatingDelta_relative_isBigO
#check @nesterov.TwoStep.alternatingDelta_relative_identity
#check @nesterov.TwoStep.alternating_mode_eventually
#check @nesterov.TwoStep.Scaling.alternating_shift_scaled_tendsto
#check @nesterov.TwoStep.Scaling.alternating_shift_scaled_atTop
#check @nesterov.TwoStep.Scaling.alternating_rate_lower

/-!
Article: Lemma E.9 [lem:spreadwit]. Spread witnesses for \(\cM\).

The literal source little-o hypotheses use the actual attained maxima of the mixed symbol and cross-characteristic magnitude on the band. They imply finite band-supported feasible atoms and strict minimizer reserve. A genuine smooth strongly convex objective and nonzero rest start in real dimension 2J+1 are fixed before every horizon, giving the stated geometric lower bound and the actual from-rest rate bound. Phase defect, product bounds and the continuous polar extension are derived rather than assumed.
-/
#check @nesterov.TwoStep.Spread.bandMaximum_isGreatest
#check @nesterov.TwoStep.Spread.littleO_rpow_iff_cubic_ratio
#check @nesterov.TwoStep.Scaling.spread_witness_from_maxima
#check @nesterov.TwoStep.Scaling.spread_witness
#check @nesterov.TwoStep.RestLowerWitness

/-!
Article: Lemma E.10 [lem:quadboundary]. Quadratic constant up to the boundary.

The actual attained quadratic maximum has the exact boundary coefficient min(cQ,cpi), including infinite cpi. The proof uses all curvatures, both signs of real roots and complex modes, with the original finite/infinite margin hypotheses.
-/
#check @nesterov.TwoStep.Scaling.quadratic_boundary_coefficient_tendsto
#check @nesterov.TwoStep.Scaling.quadratic_boundary_coefficient_tendsto_infinite

/-!
Article: Corollary E.11 [cor:frontier]. Ceilings at fixed extrapolation.

All five clauses concern actual rates. The fixed-tau quadratic price needs no convergent beta or step; acceleration forces the sharp sqrt(2) quadratic ceiling. Actual strict-bulk constants have the stated unattained supremum, reached at the boundary with the exact alternating cutoff. Actual limsup pairs are dominated by the stated arc and every arc point is realized by a stable family. Literal liminf at least one forces all three physical slow parameters to converge to (3,2,1/2), without assuming their convergence beforehand.
-/
#check @nesterov.TwoStep.fixed_tau_quadratic_limsup
#check @nesterov.TwoStep.accelerated_quadratic_limsup
#check @nesterov.TwoStep.actual_bulk_frontier
#check @nesterov.TwoStep.Scaling.optimal_boundary_constants
#check @nesterov.TwoStep.Scaling.frontier_limsup_pair
#check @nesterov.TwoStep.frontier_arc_attained
#check @nesterov.TwoStep.optimal_parameters_tendsto

/-!
Article: Remark E.12 [rem:onelayer]. One-atom spectra in the layer.

For every c above Lambda-positive/2, with no added upper restriction on c, an actual singleton with zero charge is feasible and has strict minimizer reserve. It gives one genuine real three-dimensional from-rest objective/start valid at every horizon and the actual rate lower bound. The literal kappa from-rest coefficient has the stated extended-real limsup ceiling min(cF,Lambda-positive/2), with the exact solid/dashed comparison.
-/
#check @nesterov.TwoStep.Scaling.layer_one_atom
#check @nesterov.TwoStep.Scaling.layer_one_atom_coefficient_le
#check @nesterov.TwoStep.Scaling.layer_one_atom_limsup
#check @nesterov.TwoStep.Scaling.layer_one_atom_kappa_limsup
#check @nesterov.Layer.mixedConstant
#check @nesterov.Layer.constant_le_mixedConstant
#check @nesterov.Layer.figure_mixed_domain

/-!
Article: Theorem F.1 [thm:robust]. Robust momentum.

The original closed design-rate interval yields an admissible stable tuning. Both endpoint characteristic factorizations and the exact nonnegative symbol are proved. Strict positivity on every larger circle gives the exact full, from-rest and quadratic rate, including TMM where the design-circle symbol is identically zero. Scaling restores arbitrary positive L; the right-endpoint queries execute gradient descent.
-/
#check @nesterov.Robust.ofInterval
#check @nesterov.Robust.Design.tuning
#check @nesterov.Robust.Design.stable
#check @nesterov.Robust.Design.characteristic_mu
#check @nesterov.Robust.Design.characteristic_L
#check @nesterov.Robust.Design.design_symbol
#check @nesterov.Robust.Design.design_symbol_nonneg
#check @nesterov.Robust.Design.positive_circle
#check @nesterov.Robust.Design.exact_rates
#check @nesterov.Robust.Design.scaled_stable
#check @nesterov.Robust.Design.scaled_exact_rates
#check @nesterov.Robust.Design.tmm_zero_symbol
#check @nesterov.Robust.tmm_exact_rates
#check @nesterov.Robust.Design.gd_queries

/-!
Article: Lemma F.2 [lem:cornerexp]. Expansions at the corner.

All six exact member-parameter coefficient expansions have compact-uniform O(epsilon squared) remainders. Their limiting tail and mixed-symbol forms are jointly uniform in test constant and frequency. The exact P0 identity, slow/fast characteristic estimates and alternating-root expansion preserve the source orders. The root expansion requires no positive limiting stability margin.
-/
#check @nesterov.Corner.first
#check @nesterov.Corner.correction
#check @nesterov.Corner.coefficient_exact
#check @nesterov.Corner.uniform_second_order
#check @nesterov.TwoStep.Scaling.corner_coefficient_uniform
#check @nesterov.TwoStep.Scaling.corner_cubic_uniform
#check @nesterov.TwoStep.Scaling.corner_tail_uniform_joint
#check @nesterov.TwoStep.Scaling.corner_mixed_uniform_joint
#check @nesterov.TwoStep.P0
#check @nesterov.Corner.slow_endpoint_exact
#check @nesterov.Corner.fast_endpoint_exact
#check @nesterov.Corner.largest_gap_exact
#check @nesterov.Corner.uniform_endpoint_remainder
#check @nesterov.TwoStep.Scaling.corner_S_tendsto
#check @nesterov.TwoStep.Scaling.corner_root_exact
#check @nesterov.TwoStep.Scaling.corner_root_scaled_tendsto

/-!
Article: Lemma F.3 [lem:nearcorner]. Near the corner.

Exact tail and mixed identities with jointly compact-uniform remainders tending to zero, without bounds on alpha or the margin. All characteristic endpoint identities and uniform slow/fast errors are proved, together with the derivative limit at minus one.
-/
#check @nesterov.TwoStep.Scaling.near_tail_exact
#check @nesterov.TwoStep.Scaling.near_mixed_exact
#check @nesterov.TwoStep.Scaling.near_tail_error_uniform
#check @nesterov.TwoStep.Scaling.near_mixed_error_uniform
#check @nesterov.TwoStep.P0
#check @nesterov.TwoStep.Scaling.near_slow_characteristic_exact
#check @nesterov.TwoStep.Scaling.near_fast_characteristic_exact
#check @nesterov.TwoStep.Scaling.near_slow_error_uniform
#check @nesterov.TwoStep.Scaling.near_fast_error_uniform
#check @nesterov.TwoStep.Scaling.near_corner_negative_derivative
#check @nesterov.TwoStep.Scaling.stability_gap_exact

/-!
Article: Lemma G.1 [lem:struct]. Structure of \(L_\tau\).

The exact affine dependence on both source variables, zero-step and maximal-step factorizations, diagonal norm-square identity and threshold gap are polynomial identities. The multiplier square and its diagonal/endpoint factors retain the literal source lag-two weight.
-/
#check @nesterov.FiniteCondition.Ltau_interpolate
#check @nesterov.FiniteCondition.Ltau_affine_step
#check @nesterov.FiniteCondition.Ltau_zero_step
#check @nesterov.FiniteCondition.Ltau_maxStep
#check @nesterov.FiniteCondition.diagonal_unit
#check @nesterov.FiniteCondition.thresholds_gap
#check @nesterov.FiniteCondition.multiplier_square
