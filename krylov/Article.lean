import krylov

/-!
# Adaptive Krylov Methods under Hessian Variation: ordered article statements

Every numbered theorem, lemma, proposition, corollary and definition appears
in PDF order, with its printed number, title and stable TeX label. The comments
record actual hypotheses and translations of physical/canonical coordinates,
operator scenarios, function realizations and query counts. `ArticleMap.md`
has the same references and the additional mathematical scope notes.
All supporting modules are included in `krylov.Check` and its axiom audit.
-/

/-!
Article: Definition 2.1 [def:model]. Observations and variation.

Exact segment and radial observation models, canonical increments and budgets.

OperatorTrajectory.update is the printed segment equation. ErrorTrajectory constructs the radial gradient; positive-base root reconstruction and invertible congruence preserve the relative budget.
-/
#check @krylov.Secant.OperatorTrajectory
#check @krylov.Secant.ErrorTrajectory
#check @krylov.Secant.canonicalIncrement_reconstruct
#check @krylov.Secant.observedBudget
#check @krylov.Secant.interiorBudget
#check @krylov.Secant.maximumBudget
#check @krylov.Secant.relativeBudget_congruence

/-!
Article: Definition 2.2 [def:latest]. Latest model and observed defect.

The latest symmetric window model, skew defect and diagonal normalization.

The ordered finite index implements min/max newer observations. The canonical defect is used only on positive diagonal data in the article.
-/
#check @krylov.Secant.latest
#check @krylov.Secant.defect
#check @krylov.Secant.canonicalDefect
#check @krylov.Secant.latest_isSymm

/-!
Article: Lemma 2.3 [lem:flag]. Secant flag.

All three exact secant-flag identities.

flag_identities assumes only symmetric actual segment operators, no independence or positivity; its p=0 sums are empty.
-/
#check @krylov.Secant.flag_identities

/-!
Article: Theorem 2.4 [thm:window]. Unresolved curvature.

Loewner uncertainty envelope and sharp hidden-curvature information radius.

The lower twins use independent nonempty columns, a positive base, nonnegative budgets and W<1. Empty columns instead have information radius zero. The rank-one twin formula is restricted to nonempty windows.
-/
#check @krylov.Secant.window_loewner_bound
#check @krylov.Secant.hiddenSequence_canonical_rankOne
#check @krylov.Secant.window_hidden_scenarios
#check @krylov.Secant.window_information_lower
#check @krylov.Secant.conjugate_window_information_radius
#check @krylov.Secant.empty_window_information_radius

/-!
Article: Definition 2.5 [def:classes]. Information classes.

Nonanticipating probed, one-gradient and oblivious information classes.

The raw policies receive observed histories only; span restrictions, global quadratic consistency and primitive C2 coefficient charts are distinct fields. Exact-search accounting is idealized operator information, with actual costs separately defined.
-/
#check @krylov.Methods.ProbedMethod
#check @krylov.Methods.OneGradientMethod
#check @krylov.Methods.ProbedClass
#check @krylov.Methods.SmoothProbedClass
#check @krylov.Methods.ObliviousClass
#check @krylov.Methods.ObservedRule
#check @krylov.Methods.CorrectionProgram.run_regular
#check @krylov.Methods.probedCost_run
#check @krylov.Methods.oneGradientCost_run

/-!
Article: Definition 2.6 [def:methods]. FC and RFC.

Observed FC directions and the canonical-defect-gated RFC correction.

The data-only inverse defines the direction, and successful solves yield its conjugacy. RFC gates the old retained window and constructs the augmented correction from the current probe. Invoked inverse domains remain hypotheses in the article.
-/
#check @krylov.Methods.conjugacyDirection
#check @krylov.Methods.conjugacyDirection_conjugate
#check @krylov.Methods.windowModel
#check @krylov.Methods.fcMethod
#check @krylov.Methods.rfcMethod

/-!
Article: Theorem 3.1 [thm:A]. Full-conjugacy response.

Actual defined FC cycle, uniform quadratic remainder and sharp spectral coefficient.

The physical response theorem assumes genuine nonzero search/solve domains, positive spectral interval, full active count and small actual increment sum. Its constants depend only on dimension/condition ratio; attaining paths and worst-reference asymptotics have the printed quantifier order.
-/
#check @krylov.Stability.fullFC_interior_quadratic_response
#check @krylov.Variation.spectral_response_christoffel
#check @krylov.Variation.spectral_response_attained
#check @krylov.Stability.fcWorstRatio_upper
#check @krylov.Stability.fcWorstRatio_asymptotic

/-!
Article: Theorem 3.3 [thm:C]. Second-order minimax bound.

Actual RFC second-order expansion and unknown-base one-correction minimax.

The infimum uses genuine span-restricted nonanticipating globally CG-consistent one-correction strategies. The common reference tube precedes every budget profile, including zero profiles. Normalized real risks are derived from finite ENNReal source suprema.
-/
#check @krylov.Correction.full_canonical_second_order
#check @krylov.Correction.compact_scenario_cubic_tube
#check @krylov.Information.OneCorrectionCGStrategy
#check @krylov.Information.oneCorrection_minimax_bracket
#check @krylov.Information.oneCorrection_minimax_asymptotic

/-!
Article: Definition 3.4 [def:GRFC]. Gated RFC.

Observed normalized spectral gate and its scaling invariances.

The canonical-defect gate is on the old retained window; the additional eigenvalue gate is on the augmented diagonal-normalized model. Common gradient and positive operator scaling preserve actual histories and gate branches.
-/
#check @krylov.Correction.gatedMethod
#check @krylov.Correction.gatedMethod_oneCorrection
#check @krylov.Correction.gatedMethod_consistent
#check @krylov.Correction.matrixSpectralGate_congruence
#check @krylov.Correction.gated_scalar
#check @krylov.Correction.gated_curvature_scalar

/-!
Article: Theorem 4.1 [thm:exact]. One-gradient minimax bound.

Exact physical fixed-fibre one-gradient minimax, attained by harmonic final trials.

The lower bound quantifies all actual span-restricted one-gradient methods, without CG consistency, and uses the two actual endpoint completions. Upper bounds allow arbitrary positive earlier trials. The output is virtual, not an extra evaluated query.
-/
#check @krylov.OneGradient.fibre_method_endpoint_lower
#check @krylov.OneGradient.xrfc_fibre_harmonic_upper
#check @krylov.OneGradient.fibre_exact_minimax
#check @krylov.OneGradient.harmonic_reciprocal_pivots

/-!
Article: Theorem 4.3 [thm:radau]. Window curvature completion.

Physical arbitrary-window feasibility, attained curvature interval and unique midpoint trial.

Independent S and d outside its range are explicit. Singular shifted blocks and their range conditions are retained. Full-action and Gram-data curvature sets coincide; clipping improves only a consistent positive scalar estimate.
-/
#check @krylov.Completion.window_completion_feasible_iff
#check @krylov.Completion.window_rayleigh_interval
#check @krylov.Completion.full_action_same_window_curvatures
#check @krylov.Completion.window_trial_minimax
#check @krylov.Completion.clip_curvature_trial_error

/-!
Article: Theorem 5.1 [thm:amplification]. Sharp amplification.

Sharp infinite and preterminal design limits and the finite-condition upper bound.

exists_full_sharp_limit constructs the separating graph rather than assuming an optimizer. The preterminal statement requires n times mesh to diverge; the finite upper and decimal values use the same feedback constant. See the appendix limit/optimizer/certificate declarations for the components.
-/
#check @krylov.Asymptotics.exists_full_sharp_limit
#check @krylov.Asymptotics.preterminal_optimalValue_scaled_tendsto
#check @krylov.Asymptotics.infinitePowerValue_sharp_upper

/-!
Article: Theorem 6.1 [thm:ss1F]. Trapezoid defects improve the secant R-order bound.

Exact SS1-F oldest-pair coefficients, improved R-order and continuous-third-derivative branch.

The recursive sequence, convergence, uniform normalized-window gain and arbitrary split condition are genuine source hypotheses. Canonical transport and centered split identities recover arbitrary x*. The scalar branch is included, and the conclusion is a lower R-order guarantee.
-/
#check @krylov.Convergence.ss1FSequence_printed_sharp_asymptotic
#check @krylov.Convergence.ss1FSequence_improved_rorder
#check @krylov.Convergence.ss1FSequence_continuous_oldest_product
#check @krylov.Convergence.ss1FSequence_centered_coordinate
#check @krylov.Convergence.ss1FObservedSequence_centered_physical_rorder

/-!
Article: Theorem 7.1 [thm:XR]. Quadratic identity and global convergence.

Quadratic virtual/reference identities and actual safeguarded global stationarity.

Both policies have literal accepted/rejected observation-stream induction. Before the window is full, each nonzero stored trial raises its Krylov dimension; the full-atom assumption derives the n-pair terminal window and the next minimizing query. Acceptance decisions are arbitrary for these identities; Armijo acceptance of that full query is a separate conclusion for sigma_A<1/2 at a nonstationary anchor. Translation handles arbitrary initial points. The n+1-gradient count refers to the virtual output, followed by the full query unless already evaluated. The global theorem applies to any model through the safeguarded one-probe executor, including practicalRun. The stationarity rate counts accepted outer steps.
-/
#check @krylov.XR.algorithmRun_global
#check @krylov.XR.practicalRun_global
#check @krylov.XR.quadratic_full_query_accepted
#check @krylov.XR.practical_quadratic_virtual_reference
#check @krylov.XR.practical_quadratic_trial_reference
#check @krylov.XR.practical_quadratic_full_reference
#check @krylov.XR.quadratic_observation_run_reference
#check @krylov.XR.quadratic_full_query
#check @krylov.XR.practical_quadratic_observation_run_reference
#check @krylov.XR.practical_quadratic_observation_run_terminal
#check @krylov.XR.practical_quadratic_full_query_accepted
#check @krylov.XR.practical_rawObservationRun_shift
#check @krylov.XR.practicalModel_shift
#check @krylov.XR.practical_quadratic_actual_trial

/-!
Article: Theorem 7.3 [thm:grow]. Transition to a full secant window.

Conditional growth to a full ordinary secant window and SS1 rate.

G1–G4 are local derivative, convergence, incoming-window independence, actual partial-trial adequacy and fixed safeguard bounds. Both literal trial policies derive retention, first-unit acceptance, capacity growth and chronological SS1 execution. The ordinary method has F off. The physical rate and sharp product use the true Hessian norm, sigmaH=sigma_flat sqrt(lambda_min/lambda_max), and the transported Hessian Lipschitz constant. Initially full memory uses no G3; its exported constants depend only on dimension, independence and the limiting Hessian.
-/
#check @krylov.XR.GrowthSource.clean_phase
#check @krylov.XR.GrowthSource.eventually_maximum_window
#check @krylov.Convergence.selected_source_full_XR_physical_rorder
#check @krylov.XR.PracticalGrowthSource.first_accepted
#check @krylov.XR.PracticalGrowthSource.eventually_maximum_window
#check @krylov.Convergence.practical_source_full_XR_physical_rorder
#check @krylov.Convergence.practical_source_full_XR_sharp_product
#check @krylov.XR.practical_initial_full_XR_original_rorder
#check @krylov.XR.PracticalGrowthSource.clean_phase

/-!
Article: Corollary 7.4 [cor:xrF]. XR-F in the superlinear phase.

Conditional XR-F transition, eventual inactive value gates and SS1-F rate.

Exact endpoint values and the additional Lipschitz-third-derivative assumptions give the selected-model gates and the literal chronological SS1-F recursion. The size test omits individual diagonal terms; the corrected Hermitian gate is separate. Both eventually pass. Model-metric and Euclidean splits, spectral and practical trial policies, and initially full memory without G3 have actual execution adapters. The physical guaranteed order is tau1(dimension).
-/
#check @krylov.XR.algorithmRun_eventually_corrected_gates
#check @krylov.Convergence.selected_source_full_XRF_physical_rorder
#check @krylov.XR.euclidean_initial_full_XRF_physical_rorder
#check @krylov.XR.PracticalGrowthSource.corrected_gates
#check @krylov.Convergence.practical_source_full_eq_ss1FSequence
#check @krylov.Convergence.practical_source_full_XRF_physical_rorder
#check @krylov.XR.practical_initial_full_XRF_original_rorder
#check @krylov.XR.euclideanPracticalRun_global
#check @krylov.XR.EuclideanPracticalGrowthSource.first_accepted
#check @krylov.XR.EuclideanPracticalGrowthSource.eventually_maximum_window
#check @krylov.XR.EuclideanPracticalGrowthSource.corrected_gates
#check @krylov.Convergence.euclideanPractical_source_full_eq_ss1FSequence
#check @krylov.Convergence.euclideanPractical_source_full_XRF_physical_rorder
#check @krylov.XR.euclideanPractical_initial_full_XRF_original_rorder

/-!
Article: Proposition 7.5 [prop:practical-trial]. Trial-policy invariants.

Practical trial-policy invariants, virtual quadratic CG form and global stationarity.

The selected window/model bookkeeping is independent of the scalar. Faithful quadratic data plus the span, anchor and capacity hypotheses give the raw CG decomposition. The full branch has no scalar. practicalRun_global uses the same exact-real safeguarded executor; it does not assume local adequacy.
-/
#check @krylov.XR.practicalModel_window
#check @krylov.XR.practicalModel_full
#check @krylov.XR.practical_quadratic_virtual_reference
#check @krylov.XR.practical_quadratic_trial_reference
#check @krylov.XR.practical_quadratic_full_reference
#check @krylov.XR.practicalRun_global

/-!
Article: Lemma A.1 [apA:galerkin]. Window calculus.

Window correction algebra, robust residuals, compression/support dualities and Schur completion.

All six printed parts are separate proved statements: actual inverse correction algebra; self-adjoint uncertainty balls with critical-case minimizers; correlated compressions; two-scenario/reflection lower bounds; spectral/Frobenius lp supports; singular-range block completion and exact scalar endpoints. Invertibility, positivity and finite nonzero-dimensional unit support are retained.
-/
#check @krylov.Secant.predicted_correction
#check @krylov.Secant.correction_anchor
#check @krylov.Secant.canonical_corrected_gradient
#check @krylov.Secant.matrix_repeated_correction_order
#check @krylov.LinearAlgebra.robust_residual_isGreatest
#check @krylov.LinearAlgebra.robust_identity_isLeast
#check @krylov.LinearAlgebra.robust_identity_small_iff
#check @krylov.LinearAlgebra.robust_identity_large_iff
#check @krylov.LinearAlgebra.robust_identity_critical_iff
#check @krylov.LinearAlgebra.matrix_compression_action
#check @krylov.LinearAlgebra.reflected_fibre_radius
#check @krylov.LinearAlgebra.two_scenario_value_bounds
#check @krylov.LinearAlgebra.spectral_lp_budget_duality
#check @krylov.LinearAlgebra.frobenius_lp_budget_duality
#check @krylov.LinearAlgebra.supported_nuclear_duality
#check @krylov.LinearAlgebra.block_completion_iff
#check @krylov.LinearAlgebra.hidden_entry_centre_width
#check @krylov.LinearAlgebra.hidden_entry_feasible

/-!
Article: Lemma A.2 [lem:consistent]. CG-consistency.

Quadratic CG consistency of FC/RFC and full-memory XRFC.

Positive newest-retaining memory gives genuine FC/RFC domains, zero corrections and active-count stopping. XRFC uses arbitrary nonzero data-dependent trials, obtains true independent stored spans and reaches the virtual minimizer after n+1 gradients; queried anchors can differ.
-/
#check @krylov.Methods.fullFC_consistent
#check @krylov.Methods.slidingFC_consistent
#check @krylov.Methods.rfcMethod_consistent
#check @krylov.Methods.restartedFC_static
#check @krylov.Methods.restartedRFC_static
#check @krylov.Methods.xrfc_full_basis
#check @krylov.Methods.xrfc_full_reference
#check @krylov.Methods.xrfc_full_evaluated
#check @krylov.Methods.xrfc_full_next_correction
#check @krylov.Methods.xrfc_full_terminates

/-!
Article: Lemma A.3 [apA:lem:flagcd]. Canonical flag identities.

Exact canonical flag transport and first-order normalized defect formulas.

The square transport needs invertible S; the asymptotic p-column form uses true reference CG columns, O(increment) perturbations and positive reference step energies. Normalizing the measured diagonal changes only the quadratic remainder.
-/
#check @krylov.Secant.physical_canonical_flag_identities
#check @krylov.Secant.canonical_flag_first_order
#check @krylov.Secant.canonicalDefect_normalization_order
#check @krylov.Secant.canonical_defect_budget
#check @krylov.LinearAlgebra.matrix_commutator_norm

/-!
Article: Lemma A.4 [lem:transfer]. Defect transfer and reconstruction.

Exact defect transfer and reconstruction from old-step residuals.

The staircase identity keeps the old-image pairing until actual retained conjugacy makes it zero. The final reconstruction requires the augmented step matrix square and invertible; it is not asserted for rank-deficient windows.
-/
#check @krylov.Secant.staircase_residual
#check @krylov.Secant.conjugate_staircase
#check @krylov.Secant.physical_defect
#check @krylov.Secant.residual_reconstruction

/-!
Article: Proposition A.5 [prop:dict]. The realization dictionary and the static direction.

Frozen Jacobi/CG dictionary, fixed-realization static gain and adaptive static termination.

Raw negative-coupling Jacobi data derive the measured CG recurrence and determinant polynomials. Terminal Chebyshev exactness fixes nodes with free weights. Fixed coefficients have the kernel derivative/static amplification; adaptive globally consistent methods instead terminate on every positive static quadratic.
-/
#check @krylov.Reference.CG.displacement_frozen
#check @krylov.Realization.raw_ldl
#check @krylov.Realization.raw_cg_determinant_eval
#check @krylov.Realization.raw_query_eval
#check @krylov.Realization.raw_injection_eval
#check @krylov.Realization.raw_exact_spectrum
#check @krylov.Realization.fixed_static_sum_rule
#check @krylov.Realization.fixed_top_amplification
#check @krylov.Realization.endpoint_relative_coefficient
#check @krylov.Methods.cgConsistent_static_stopping

/-!
Article: Proposition A.7 [prop:conv]. Converting the two perturbation budgets.

First-order conversion of query drifts and physical secant increments.

The injection formula is on the common CG reference; minimum symmetric-image norm gives the inverse conversion denominator. Actual compact conversion wrappers derive trajectory regularity instead of assuming a response formula. A short step may enlarge the budget.
-/
#check @krylov.Realization.cg_secantInjection
#check @krylov.Realization.minimum_secant_norm
#check @krylov.Realization.compact_metric_secantConversion
#check @krylov.Stability.smoothProbed_compact_secantConversion

/-!
Article: Lemma A.8 [apG:mss]. Model error and the oldest pair.

Physical model-error identity, oldest-column distance and superlinear model query.

An invertible normalized basis gives the exact inverse congruence. Uniform least gain and vanishing corrected data error imply inverse convergence. The sharper leading oldest-diagonal estimate requires its stated O(q) and little-o remainder hypotheses.
-/
#check @krylov.Secant.physical_normalized_model_error
#check @krylov.Secant.physical_normalized_model_bound
#check @krylov.Secant.oldest_model_split
#check @krylov.LinearAlgebra.oldest_column_distance
#check @krylov.Secant.physical_model_step_identity
#check @krylov.Secant.physical_corrected_model_error
#check @krylov.Secant.conditioned_model_convergence
#check @krylov.Secant.oldest_model_asymptotic_bound

/-!
Article: Lemma B.1 [lem:U]. Uniform remainders.

Compact-uniform weighted Taylor remainders and homogeneous cone extension.

Actual smooth coefficient charts and genuine reference domains provide the required C-r map. Coefficient regularity/top-order continuity and Lipschitz refinements are separate results. Cone extension requires degree-one outputs with degree-zero decisions.
-/
#check @krylov.Stability.compact_reference_taylor
#check @krylov.Stability.compact_taylorCoefficient_lipschitz
#check @krylov.Stability.compact_topCoefficient_lipschitz
#check @krylov.Stability.homogeneous_taylor_remainder_bound
#check @krylov.Stability.quadraticFC_compact_cone_taylor
#check @krylov.Stability.quadraticRFC_compact_cone_taylor
#check @krylov.Stability.quadraticXRFC_compact_cone_taylor
#check @krylov.Stability.smoothProbed_compact_cone_taylor
#check @krylov.Stability.full_history_virtual_contDiffAt

/-!
Article: Lemma B.2 [lem:aggregate]. Aggregated compressions.

Sharp joint spectral and Frobenius aggregation bounds.

Projectors, a common orthogonal unit vector, self-adjoint increments and nonnegative actual budgets are explicit. Planar Minkowski preserves the cross/action tradeoff; simultaneous attainment additionally requires one common old unit direction.
-/
#check @krylov.LinearAlgebra.aggregated_compression_action
#check @krylov.LinearAlgebra.aggregated_hidden_diagonal
#check @krylov.LinearAlgebra.frobenius_aggregated_compression
#check @krylov.LinearAlgebra.spectral_aggregate_sharpness
#check @krylov.LinearAlgebra.frobenius_aggregate_sharpness

/-!
Article: Lemma B.3 [lem:projected-residual]. Projected residual after a correction.

Projected and recorded RFC residual orders with contaminated secant pairs.

The finite quantitative estimate retains normalized model/frame eigenvalue bounds and the stated recording condition. Actual RFC execution gives the true pair contamination identity and quadratic projected residuals; it is not assumed as a source expansion.
-/
#check @krylov.Methods.normalizedRFC_projected_estimates
#check @krylov.Methods.scheduled_correction_pair_identity
#check @krylov.Stability.quadraticRFC_canonical_projection_orders
#check @krylov.Stability.quadraticRFC_pair_orders

/-!
Article: Lemma B.4 [lem:terminal-fibre]. A two-dimensional data fibre.

Exact common terminal data fibre and two-scenario correction radius.

Positive physical operators and |x|<1 give the shared last line search. Genuine global CG consistency forces the common previous transcript. The lower bound applies to arbitrary common corrections, and the centre formula is exact.
-/
#check @krylov.Secant.terminal_data_fibre
#check @krylov.Secant.physicalTerminal_normalized_last_probe
#check @krylov.Secant.terminalSegments_output
#check @krylov.Secant.terminal_line_search
#check @krylov.Secant.terminal_two_scenario_lower
#check @krylov.Secant.terminal_centre_residuals

/-!
Article: Lemma B.5 [apB:lem:nostag]. No stagnation.

CG nonstagnation, one-step energy contraction and step-energy lower bounds.

The strict active prefix is k below the number of active atoms. A positive spectral band supplies the condition ratio; the weaker inverse-kappa bound follows from the sharp contraction factor.
-/
#check @krylov.Reference.cg_nonstagnation
#check @krylov.Reference.cg_error_contract
#check @krylov.Reference.cgEnergy_lower
#check @krylov.Reference.cgEnergy_lower_condition

/-!
Article: Lemma B.6 [lem:chris]. Energy and Christoffel functions.

CG energy profile, Christoffel minimum and moment determinant formulas.

The full spectral probability measure is that of the initial canonical error. Active-count and moment nondegeneracy hypotheses give the determinant ratio; the terminal zero is handled separately. Energy drop equals CG length times squared gradient norm.
-/
#check @krylov.Reference.cg_energy_christoffel_all
#check @krylov.Reference.cgEnergy_tail
#check @krylov.Reference.canonicalCGStep_tail
#check @krylov.Reference.christoffel_moment_determinant
#check @krylov.Reference.terminal_moment_determinant
#check @krylov.Reference.cgEnergy_eq_length_norm

/-!
Article: Corollary B.7 [s3:cor:cf]. Correction-free methods are first order.

Exact correction-free adverse path and first-order minimax interval.

Every globally CG-consistent correction-free source policy shares the same actual transcript on the signed planar path. W<1 ensures positive operators. The lower price and FC sharp upper are genuine response risks, not assumed linear surrogates.
-/
#check @krylov.Variation.correctionFree_terminal_vector
#check @krylov.Variation.fc_firstVariationPrice_eq
#check @krylov.Variation.correctionFree_minimax_interval

/-!
Article: Lemma B.8 [apB:lem:UAsteps]. Perturbed conjugacy and line steps.

Step-length-independent perturbed conjugacy and uniform actual FC stability.

The exact inverse solve gives normalized canonical angle at most the true old operator deviation. Uniform step bounds use a defined actual cycle, small drift and the physical initial-error factor, without a minimum active energy assumption.
-/
#check @krylov.Stability.fullFC_canonical_angle
#check @krylov.Stability.fullFC_uniform_next_step_scale
#check @krylov.Stability.fullFC_uniform_steps_weighted_scale
#check @krylov.Stability.fullFC_uniform_direction_flag_scale

/-!
Article: Proposition B.9 [prop:HS]. Hilbert--Schmidt budgets.

Sharp joint Hilbert-Schmidt response coefficient.

The symmetric cross block costs two Frobenius squares, producing omega/sqrt(2). Attaining increments are constructed on the actual CG frame. The design identity uses the energy spectral measure and gamma=1 criterion.
-/
#check @krylov.Variation.frobenius_response_le
#check @krylov.Variation.frobenius_response_attained
#check @krylov.Cost.actual_hs_response_attained
#check @krylov.Cost.hsWorstCoefficient_eq_design

/-!
Article: Definition B.10 [s3:def:phi]. Continuation polynomials and common tilt.

Frozen continuation/direction polynomials and common tilt.

Lean phi/psi use start j and offset k, so article endpoint m corresponds to k=m-j. Initial states and both recurrences are definitional. The commonTilt is the printed finite measured displacement pairing.
-/
#check @krylov.Envelope.phi
#check @krylov.Envelope.psi
#check @krylov.Envelope.frozen_displacement_formula
#check @krylov.Envelope.commonTilt

/-!
Article: Theorem B.11 [thm:E]. Variation before Krylov exhaustion.

Actual compact-uniform pre-exhaustion decomposition and common norm-trace first variation.

Primitive globally consistent smooth information classes derive the genuine filtration. The response has a common unexplored component and method-dependent explored component. The scalar first-order norm expansion retains a positive reference final error and its near-exhaustion denominator.
-/
#check @krylov.Envelope.actual_compact_envelope
#check @krylov.Envelope.commonTransverseResponse_increment_sum
#check @krylov.Envelope.actual_compact_norm_trace
#check @krylov.Envelope.orthogonal_envelope_norm

/-!
Article: Lemma B.12 [apB:lem:filtration]. Filtration.

Actual observed-vector filtration, frozen step displacement and gradient-jet balance.

The signatures quantify actual histories and primitive smooth-policy charts, not a presumed output jet. Their reference nonstagnation and observed-span restrictions match H1-H3; all finite correction observations are included.
-/
#check @krylov.Envelope.actual_observation_filtration
#check @krylov.Envelope.actual_frozen_filtration
#check @krylov.Envelope.actual_frozen_step
#check @krylov.Envelope.probed_gradient_jet_balance

/-!
Article: Corollary B.13 [thm:E1]. Virtual-launch envelope.

Virtual XRFC output envelope with actual trial defects.

The reference has at least m+1 active atoms and the actual data trial chart is C2 and positive. The object is outputGradient, which becomes a function gradient only under a function realization. Exact reference trials cancel every trial term.
-/
#check @krylov.Envelope.xrfc_source_envelope_response
#check @krylov.Envelope.xrfc_source_norm_envelope
#check @krylov.Envelope.xrfc_compact_virtual_envelope
#check @krylov.Envelope.xrfc_exact_trials_envelope_response

/-!
Article: Corollary B.14 [cor:lm]. Realization dependence before and near exhaustion.

Realization-dependent norm comparison and FC/RFC transverse difference.

The linear max bound is valid at a=0; the quadratic-over-common-norm bound requires a>0. The displayed comparison treats a=0 separately. On a fixed nonexhausted compact reference family the common first norm variations cancel; near exhaustion only the displayed conditional bound applies.
-/
#check @krylov.Envelope.orthogonal_norm_comparison
#check @krylov.Envelope.orthogonal_norm_comparison_quadratic
#check @krylov.Envelope.compact_budget_method_quadratic
#check @krylov.Envelope.fullFC_sub_fullRFC_transverse

/-!
Article: Proposition B.15 [prop:phi]. Continuation determinants.

Measured continuation determinant, simple Ritz zeros, sign and monotonicity.

The measured positive Jacobi prefix and its Schur complement give the true determinant polynomial. Nonempty prefix and 0<=j<=m are explicit; the stronger active-count condition makes its Ritz spectrum lie strictly inside the source interval. The j=m polynomial is constant.
-/
#check @krylov.Envelope.lanczos_phi_suffix_determinant
#check @krylov.Envelope.lanczos_phi_schur_determinant
#check @krylov.Envelope.lanczos_phi_ritz_properties
#check @krylov.Envelope.cg_phi_zeros_interior

/-!
Article: Theorem B.16 [thm:select]. Minimax transverse variation.

Attained transverse minimax over globally consistent smooth information classes.

The actual infimum is an IsLeast over genuine SmoothProbedClass, with a separate one-correction subclass. Absorbed scenarios force every method; actual RFC and a final observed-model correction attain the same selection value. Nuclear duality uses the real constrained polynomial sphere.
-/
#check @krylov.Envelope.selection_minimax
#check @krylov.Envelope.selection_oneCorrection_minimax
#check @krylov.Envelope.selection_nuclear_dual
#check @krylov.Envelope.finalized_selection_value_attained

/-!
Article: Lemma B.17 [apB:lem:mu]. The information fibre and its residual.

Common tilt, absorbed quadratic shadow, invisible fresh residual and Daleckii-Krein pairing.

All five parts concern actual globally consistent primitive smooth methods. The source absorbed transcript is proved equal at first order to one literal affine quadratic. The invisible correction-free residual and final-zero dual block are conclusions, not hypotheses.
-/
#check @krylov.Envelope.actual_tilt_splitting
#check @krylov.Envelope.commonTilt_canonical_formula
#check @krylov.Envelope.source_absorbed_observation_fibre
#check @krylov.Envelope.source_absorbed_step_fibre
#check @krylov.Envelope.correctionFree_invisible_residualVariation
#check @krylov.Envelope.actual_tilt_daleckiiKrein_pairing
#check @krylov.Envelope.daleckiiKrein_last_compression_zero

/-!
Article: Proposition B.18 [apB:prop:consist]. CG-consistency is the operative hypothesis.

Reference-only consistency permits an attained zero transverse price.

The alternative source class assumes consistency only at the chosen reference. A real targeted one-correction policy has zero source variation on all scenarios, and nonnegative true risks give the attained minimum/infimum zero.
-/
#check @krylov.Envelope.reference_selection_zero_attained
#check @krylov.Envelope.reference_selection_isLeast_zero
#check @krylov.Envelope.reference_selection_infimum_zero

/-!
Article: Corollary B.19 [s3:thm:cf]. The price without a final correction.

Strict excess of correction-free transverse variation.

The lower witness is a genuine feasible source scenario and the actual worst response is attained. Positive final budget and genuine active last-step energy give the strict inequality; zero profiles remain in the weak bound.
-/
#check @krylov.Envelope.correctionFree_excess_lower
#check @krylov.Envelope.correctionFree_strict_excess

/-!
Article: Corollary B.20 [s3:cor:qn]. Gradient-norm minimax comparison.

Compact-uniform worst-gradient comparison and exact first-jet realization minimax.

The fixed competing method is genuinely smooth and globally CG-consistent. A common compact remainder tube precedes every profile. Budget-preserving absorption compares actual nonlinear suprema, with only the stated quadratic error; the exact minimax concerns the first-jet realization term.
-/
#check @krylov.Envelope.rfc_compact_worst_norm_comparison
#check @krylov.Envelope.finalized_transverse_optimal

/-!
Article: Lemma B.21 [apD:lem-model]. A modified last model.

Effect of a last-model symmetric perturbation.

The modified last model has a genuine O(omega) symmetric normalized change. Actual correction execution gives the second-order coefficient with a cubic remainder, and a diagonal old-pair change has the printed canonical decomposition.
-/
#check @krylov.Correction.full_modified_canonical_second_order
#check @krylov.Correction.referenceDiagonalChange_canonical

/-!
Article: Proposition B.22 [thm:C2]. Frobenius budgets.

Independent Frobenius-budget FC response and RFC minimax, already for known base.

frobenius_minimax_bracket quantifies known=true and false before every nonnegative profile; actual RFC attains K/sqrt(2) with a common cubic tube. These independent Frobenius budgets differ from the separate known-base single-increment spectral problem.
-/
#check @krylov.Variation.frobenius_response_attained
#check @krylov.Correction.full_canonical_frobenius_upper
#check @krylov.Information.frobenius_minimax_bracket
#check @krylov.Information.frobenius_minimax_asymptotic

/-!
Article: Proposition B.23 [thm:centre]. Latest information is the centre.

Data-preserving reflection and the latest-model information centre.

The involution preserves true probe/old correction actions. The actual admissible physical twin needs exactly the C1-C4 slack/metric conditions, with allowed intermediate replacements. Its final operators are reflected about the observed centre and the two-scenario normalized radius applies.
-/
#check @krylov.Information.Scenario.reflect_involutive
#check @krylov.Information.Scenario.reflect_probe_column
#check @krylov.Information.Scenario.reflect_intermediate_column
#check @krylov.Information.Scenario.reflect_about_latest
#check @krylov.Information.Scenario.exists_admissible_physical_twin
#check @krylov.Information.Scenario.centre_fibre_radius

/-!
Article: Corollary B.24 [s4:cor-Q]. Pre-quadratic scenarios: RFC is instance-optimal.

Pre-quadratic instance comparison and sharp inner-class minimax.

The actual natural-inner pre-quadratic twin is common to every globally consistent policy. Small window/budget and relative reference-radius bounds yield the multiplicative/additive comparison; the genuine inner minimax bracket includes degenerate profiles.
-/
#check @krylov.Information.preQuadratic_instance
#check @krylov.Information.preQuadratic_instance_additive
#check @krylov.Information.inner_oneCorrection_minimax_bracket

/-!
Article: Theorem B.25 [thm:UCq]. Uniformity and the spectral gate.

Uniform ordinary and spectrally gated RFC bounds.

Ordinary uniformity uses N except in dimensions two/three. The gated theorem concerns genuinely defined cycles and its last-step refinement requires a performed final correction. A separate source theorem makes all spectral gates pass under N. Constants precede source data and depend only on the stated dimension, condition ratio and threshold.
-/
#check @krylov.Correction.ordinary_uniformity
#check @krylov.Correction.gated_uniform_scenario_cycle
#check @krylov.Correction.gated_uniform_nonstagnating_scenario

/-!
Article: Proposition B.26 [prop:deep]. An unbounded RFC family; certified.

Actual four-dimensional affine RFC counterexample with checked data.

The exact source family has the printed base, initial gradient and strict budgets. Independently compiled rational expressions are identified with the real RFC executor; all canonical gates pass. Terminal outputs become arbitrarily large through positive definite final models.
-/
#check @krylov.Correction.deep_actual_unbounded_positive
#check @krylov.Correction.deep_actual_defect_small
#check @krylov.Correction.deep_actual_preterminal_posDef
#check @krylov.Correction.deep_unbounded_admissible

/-!
Article: Theorem C.1 [thm:I]. XRFC variation.

Actual full-memory XRFC canonical variation and sharp trial-response support.

The semantic output is the operator-model outputGradient. Actual positive C2 reference trials imply genuine nonzero stored columns and inverse domains. The finite full-source derivative and quadratic remainder use all original canonical increments including the unevaluated output segment.
-/
#check @krylov.OneGradient.xrfc_step_canonical_expansion
#check @krylov.OneGradient.xrfc_step_response_sharp
#check @krylov.OneGradient.xrfc_step_exact_canonical_quadratic

/-!
Article: Lemma C.2 [apE:Pi]. Structure of the XRFC steps.

True XRFC bidiagonal columns and exact oblique prefix-flag geometry.

All columns come from actual quadratic XRFC execution with nonzero trials. The measured diagonal equals one minus trial error and is nonzero. The printed tail coefficients, prefix span, row norm and last-amplitude identity are derived from that same bidiagonal basis.
-/
#check @krylov.OneGradient.xrfc_canonical_step_bidiagonal
#check @krylov.OneGradient.xrfc_projector_unit_columns
#check @krylov.OneGradient.xrfc_projector_matrix_norm
#check @krylov.OneGradient.xrfc_flag_row_norm_sq
#check @krylov.OneGradient.xrfc_flag_last_scalar_amplitude

/-!
Article: Lemma C.3 [s5:trial]. Trial errors.

Trial-error propagation and harmonic/arithmetic interval minimax.

Positive physical endpoint lengths, ordered nondegenerate interval and all real trial lengths give the unique harmonic and arithmetic optimizers. The factor inequalities are on the actual transformed errors; exact, overshooting and large undershooting branches retain their precise domains.
-/
#check @krylov.OneGradient.harmonic_trial_minimax
#check @krylov.OneGradient.arithmetic_estimate_minimax
#check @krylov.OneGradient.harmonic_trial_attains
#check @krylov.OneGradient.arithmetic_estimate_attains
#check @krylov.OneGradient.xrfc_trial_coefficient_abs
#check @krylov.OneGradient.overshoot_factor_lt_one
#check @krylov.OneGradient.undershoot_factor_gt_one

/-!
Article: Proposition C.4 [prop:launch]. Compressions times extrapolation distance.

Actual moving-model output expansion from C1 data.

Independent reference steps and genuine symmetric segment operators give the exact model factorization. Freezing the outer moving coefficients leaves products of two first-order vanishing factors, so C1 data suffice for the O(omega^2) remainder. The output is an abstract operator-model vector unless realized by one function.
-/
#check @krylov.OneGradient.launch_semantic_c1_actual_increment_remainder
#check @krylov.OneGradient.evaluated_launch_sharp_comparison

/-!
Article: Definition C.5 [s5:info]. Krylov information and scenarios.

The information is the actual positive operator restriction on the old Krylov flag. Prior membership is imposed on physical completions; the output budget is the own-base operator norm.

The coordinate pivot is supplied only after identifying the whole physical information fibre.
-/
#check @krylov.OneGradient.krylovInformationFibre
#check @krylov.OneGradient.fibreAdmissiblePivots
#check @krylov.OneGradient.fibreStepRatio
#check @krylov.OneGradient.fibreOutputBudget
#check @krylov.OneGradient.krylov_information_fibre_dictionary
#check @krylov.OneGradient.prior_information_fibre_dictionary

/-!
Article: Lemma C.6 [s5:fibre]. The fibre is a Gauss--Radau segment.

All positive completions, common physical CG states and the reciprocal last pivot are identified; spectral and relative-ball endpoint intervals have their true physical endpoint attainments.

Dimension n in the paper is Fin(k+1) or Fin(k+2) in wrappers. Full active spectrum supplies nonzero last direction and strict leading spectral pencils. Relative balls use 0≤ρ<1.
-/
#check @krylov.OneGradient.lanczos_completion_positive_iff
#check @krylov.OneGradient.lanczos_completion_central_ball
#check @krylov.OneGradient.physical_information_fibre
#check @krylov.OneGradient.completion_last_cg_length
#check @krylov.OneGradient.relative_ball_fibre_ratio
#check @krylov.OneGradient.physical_fibre_endpoint_eigenvectors
#check @krylov.OneGradient.spectral_prior_ratio_isLUB

/-!
Article: Lemma C.7 [apE:info]. What a one-gradient method knows before its last evaluation.

A single old-flag vector and last-direction coefficient are chosen before every completion; the actual histories and final query point agree.

OneGradientSpanRestricted is the observed-span condition in the article information class; CG consistency is not assumed for this information lemma.
-/
#check @krylov.OneGradient.one_gradient_information_history
#check @krylov.OneGradient.one_gradient_information_last_point
#check @krylov.OneGradient.one_gradient_information_decomposition

/-!
Article: Corollary C.8 [cor:quant]. Spectral and local quantification.

IsLeast quantifies the method before all reference/scenario choices, with one actual history-only harmonic policy attaining the spectral and relative-ball uniform guarantees.

The spectral reference supremum is strict for each irreducible reference. The relative-ball centre supplies actual attained endpoint adversaries; zero output radius is included.
-/
#check @krylov.OneGradient.spectral_prior_exact_uniform_minimax
#check @krylov.OneGradient.spectral_prior_two_basis_attainment
#check @krylov.OneGradient.relative_prior_exact_uniform_minimax
#check @krylov.OneGradient.observed_relative_ball_central_trial
#check @krylov.OneGradient.spectral_prior_coefficient_bounds

/-!
Article: Corollary C.9 [s5:moment]. The undetermined moment.

All supported probability measures, not only n-atomic candidates, have exactly the printed missing-moment range; the positive affine coefficient and endpoint uniqueness are proved.

The free canonical coordinate requires a positive endpoint gap. At a collapsed interval its coordinate is fixed.
-/
#check @krylov.OneGradient.missing_moment_range
#check @krylov.OneGradient.missing_moment_slope_positive
#check @krylov.OneGradient.missing_moment_closed_interval
#check @krylov.OneGradient.spectral_principal_representations
#check @krylov.OneGradient.canonical_pivot_range
#check @krylov.OneGradient.canonical_pivot_collapsed

/-!
Article: Proposition C.11 [thm:hier]. Uniform information-class separation.

Actual normalized energy-floor families force a first-order output loss for every observed-span method, while gated RFC has a uniform quadratic bound and a known base yields a mixed rω+ω² estimate.

The one-gradient lower bound is on constant prefixes; nondegeneracy/positive energy floors belong to the stated restricted reference family.
-/
#check @krylov.Cost.normalized_information_lower
#check @krylov.Correction.gated_uniform_cycle
#check @krylov.Cost.fixedCG_known_base_ball_bound

/-!
Article: Theorem D.1 [thm:B]. Mixed extrapolation criterion.

Attainment and the sharp support size are on all probability measures. The exact maximum-sensitivity equivalence, support equality and tangent upper certificate have the printed factors.

Lean Fin M indexes degrees i+1. Positive last weight rules out the zero objective; the cardinal hypothesis derives positive moment matrices rather than assuming their inverses exist.
-/
#check @krylov.Design.intervalObjective_attains_small_support
#check @krylov.Design.optimal_interval_support_card_eq
#check @krylov.Design.intervalObjective_maximum_sensitivity_equivalence

/-!
Article: Lemma D.2 [lem:chebyshev-design]. Chebyshev extrapolation design; {\cite{Greenbaum79,HoelLevine64}}.

The physical Lobatto design with absolute Lagrange weights attains the universal Christoffel maximum, and its residual equals the sech expression.

The result holds also at degree zero in Lean; the article restricts m≥1.
-/
#check @krylov.Design.chebyshev_design_extremum
#check @krylov.Design.lobattoProbability
#check @krylov.Design.epsilon_eq_sech

/-!
Article: Lemma D.4 [apC:lem:natoms]. Measures with a prescribed number of atoms.

Constructive padding by distinct atoms approximates the all-measure optimum at each prescribed N≥M+1, proving equality of actual suprema.

This is a supremum statement for exactly N atoms; it does not claim that an N-atomic maximizer always exists.
-/
#check @krylov.Design.exists_prescribed_atoms_near_optimal
#check @krylov.Design.atomicDesignValue_eq_optimalValue

/-!
Article: Lemma D.5 [apC:lem:poisson]. Poisson summation for the Chebyshev majorants.

Both literal Poisson identities have positive dual tails and the precise first exponential coefficients; a genuine elliptic integral and its standard nome give the equivalent expression.

All sums use positive indices m≥1, with the half-endpoint contribution written separately.
-/
#check @krylov.Design.poisson_remainders_eq_dual
#check @krylov.Design.poisson_remainders_pos
#check @krylov.Design.poisson_sech_remainder_asymptotic
#check @krylov.Design.poisson_sechSquared_remainder_asymptotic
#check @krylov.Design.sampledSech_elliptic_nome

/-!
Article: Definition D.6 [s3:def:string]. Strings and their reward.

The unit left atom is part of the initial state. Genuine Volterra existence and uniqueness, compact gluing, RN density, type clock and monotone exhaustion reward cover arbitrary Stieltjes strings.

Mass is represented as a measure with a unit origin atom; finite excluded endpoints are handled by local windows, not by assuming a finite total mass.
-/
#check @krylov.Strings.Mass.exists_global_state
#check @krylov.Strings.Mass.global_state_unique
#check @krylov.Strings.IsState
#check @krylov.Strings.Mass.reward
#check @krylov.Strings.TypeChange.actual_type_change

/-!
Article: Theorem D.8 [thm:value]. Optimal continuum string.

The actual all-length optimizer exists uniquely, has the stated analytic positive density, and the same mass has its canonical principal probability measure, zero atom and exact high-frequency tail.

ActualRegularMaximum is not an input optimizer certificate: the exists theorems construct it. Finite-length strings, singular mass and endpoint blowup are included among competitors.
-/
#check @krylov.Strings.exists_unique_actual_all_lengths_maximum
#check @krylov.Strings.exists_actual_regular_maximum
#check @krylov.Strings.Spectral.exists_actual_half_principal_attainment
#check @krylov.Strings.Spectral.exists_actual_half_principal_tail_attainment
#check @krylov.Certificates.exists_certified_continuum_maxima

/-!
Article: Theorem D.9 [thm:limit]. Asymptotics of the worst constant.

The exact finite-condition upper expression and both sharp infinite/finite-horizon limits use the same constructed feedback graph and genuine discrete recovery.

The finite-horizon limit explicitly assumes nθ→∞; graphBound is γ below one and 1/2 at γ=1.
-/
#check @krylov.Asymptotics.exists_full_sharp_limit
#check @krylov.Asymptotics.finiteDesignUpper
#check @krylov.Asymptotics.infinitePowerValue_half_lt_sampledSech

/-!
Article: Proposition D.11 [apC:prop:LV]. Separatrix, $\gamma\in(0,1)$.

The global graph is constructed, analytic across the saddle, and exactly the positive stable set. Actual finite first exits identify both sides of the crossing.

Exit classification applies to interior starts 0<s<s_F, as now stated. The graph definition includes both lower and upper branch wedges.
-/
#check @krylov.LotkaVolterra.exists_subcriticalGraph
#check @krylov.LotkaVolterra.SubcriticalGraph.analyticAt
#check @krylov.LotkaVolterra.SubcriticalGraph.mem_stable_set_iff
#check @krylov.LotkaVolterra.exists_lower_classified_exit

/-!
Article: Proposition D.12 [apC:prop:g1]. Separating orbit, $\gamma=1$.

The genuine endpoint separating graph has its analytic extension and unbounded U trajectory. Original-time entrance/exit sets are the two open intervals around its unique crossing.

The complement in the article is nonempty; Lean proves the stronger singleton description after uniqueness.
-/
#check @krylov.LotkaVolterra.exists_global_endpoint_graph_gap
#check @krylov.LotkaVolterra.exists_analytic_endpoint_graph
#check @krylov.LotkaVolterra.endpoint_actual_orbit_classification

/-!
Article: Lemma D.13 [apC:lem:fund]. Fundamental identity.

The actual cadlag state potential loses exactly reward, square loss, continuous singular loss and a convergent sum of positive atom losses.

The origin atom is excluded from the jump sum because it already enters the initial state; general finite endpoints are reduced to compact windows.
-/
#check @krylov.ContinuumBV.actual_fundamental_identity
#check @krylov.Strings.OptimizerFinite.optimal_window_conditions

/-!
Article: Proposition D.14 [apC:prop:digits]. Certified numerical values.

The exact printed rational crossing brackets, their actual four orbit exits and all seven strict five-significant-digit roundings follow from kernel-checked rational barriers.

The half-gamma exit adapters use the printed rational endpoints; the endpoint orbit classification supplies the other two exits.
-/
#check @krylov.LotkaVolterra.SubcriticalGraph.half_certified_crossing_bounds
#check @krylov.Certificates.endpoint_certified_crossing_bounds
#check @krylov.Certificates.half_lower_crossing_bracket_exit
#check @krylov.Certificates.half_upper_crossing_bracket_exit
#check @krylov.Certificates.certified_endpoint_orbit_exits
#check @krylov.Certificates.five_significant_derived_values

/-!
Article: Lemma D.15 [apC:lem:stieltjes]. Stieltjes strings and Christoffel functions.

The actual positive finite path operator has the full simple probability spectrum, polynomial orthogonality and exact Christoffel kernel; every prescribed nonnegative atomic probability measure is reconstructed with the stated Robin condition and norm.

Lean uses N+1 masses for article N. The sign-gauged orthogonal-polynomial recurrence gives positive physical gaps; zero belongs to the spectrum exactly at zero Robin parameter.
-/
#check @krylov.Strings.DiscreteString.spectralMeasure_orthogonality
#check @krylov.Strings.DiscreteString.spectralMeasure_christoffel
#check @krylov.Strings.DiscreteInverse.exists_string
#check @krylov.Strings.DiscreteInverse.mass_formula
#check @krylov.Strings.DiscreteInverse.gap_formula
#check @krylov.Strings.DiscreteInverse.robin_formula
#check @krylov.Strings.DiscreteInverse.robin_eq_zero_iff
#check @krylov.Strings.DiscreteString.spectralRadius_le_of_gershgorinRows

/-!
Article: Proposition D.17 [apC:prop:local]. Top solution.

Positivity of the top positions/fluxes and the terminal Robin inequality is equivalent to the actual physical operator norm bound.

The terminal flux is the physical topTerminal expression; no top-positivity certificate is assumed for the converse.
-/
#check @krylov.Strings.DiscreteString.spectralRadius_lt_iff_top

/-!
Article: Lemma D.18 [apC:lem:topimp]. Top identities.

The terminal mass inequality and strict adjacent mass-gap product follow from the true spectral norm constraint; top recurrence identities supply the two exact impedance formulas.

The final Robin term is retained in the terminal inequality.
-/
#check @krylov.Strings.DiscreteString.top_terminal_identity
#check @krylov.Strings.DiscreteString.top_bond_identity
#check @krylov.Strings.DiscreteString.top_mass_identity
#check @krylov.Strings.DiscreteString.top_gap_mass

/-!
Article: Lemma D.19 [apC:lem:B]. Monotonicity and log-Lipschitz bound.

The constructed subcritical/endpoint graphs satisfy the sharp logarithmic slope bound throughout r≥1, including the saddle via its analytic derivative.

The derivative quotient is interpreted continuously at the saddle, as in the article; graphBound has the special endpoint value 1/2.
-/
#check @krylov.Asymptotics.exists_analytic_logLipschitz_graph

/-!
Article: Lemma D.20 [apC:lem:apriori]. A priori bounds.

The physical discrete ratio lies between one and 1+Λ; the weighted logarithmic energy sum has the telescoping upper bound 1/γ.

The spectral top product constraint used by ratio_bounds is proved from the actual string norm bound in the preceding discrete-operator results.
-/
#check @krylov.Asymptotics.DiscreteString.ratio_bounds
#check @krylov.Asymptotics.DiscreteString.weighted_energy_log_sum_le

/-!
Article: Lemma D.21 [apC:lem:step]. One step, exact averages.

The genuine drift/impulse integrals give q≤k, the exact log increment, potential-loss estimate and both full logarithmic-average product bounds.

Eplus and Eminus are continuously extended at zero; the article A^I is the reciprocal of the Lean impulseAverage, so A^D/A^I becomes the displayed product.
-/
#check @krylov.Asymptotics.DiscreteString.log_bounds
#check @krylov.Asymptotics.DiscreteString.ratio_log_increment
#check @krylov.Asymptotics.DiscreteString.step_potential_ge
#check @krylov.Asymptotics.DiscreteString.bond_average_exact_bound
#check @krylov.Asymptotics.DiscreteString.site_average_exact_bound

/-!
Article: Proposition D.22 [apC:prop:tauber]. Tail without rate, general strings.

For the genuine canonical principal energy measure, a positive essential initial density limit gives both exact weighted-moment and tail equivalents.

Only local absolute continuity near the origin is required; finite/infinite physical lengths and arbitrary global mass are represented, with the principal endpoint convention fixed.
-/
#check @krylov.Strings.GeneralSpectral.principalMeasure_tail_asymptotics_of_initial_density
#check @krylov.Strings.GeneralSpectral.finiteSource_principalMeasure_tail_asymptotics

/-!
Article: Lemma E.1 [apG:sc]. Secants near a nondegenerate minimizer.

Canonical Hessian sandwich, sublevel-radius equation and expansion, sharp local Lipschitz bound and endpoint secant comparison are for genuine scalar-function derivatives.

The Dikin-ball/domain assumptions in the article are essential; the C3 midpoint expansion and tensor bound follow from the actual third derivative dictionaries.
-/
#check @krylov.Functions.standardSelfConcordant_metric
#check @krylov.Functions.standardSelfConcordant_sublevel
#check @krylov.Functions.scSublevelRadius_le_double
#check @krylov.Functions.scSublevelRadius_cubic_expansion
#check @krylov.Functions.standardSelfConcordant_hessian_lipschitz
#check @krylov.Functions.averagedHessian_endpoint_bound

/-!
Article: Lemma E.2 [apG:E]. The exact line search.

The actual unique chord minimizer exists and is interior, stationary and within all printed radius/step bounds.

Zero directions are included; nonzero-direction compactness is proved in the scalar chord parameter. Canonical centering identifies x*=0 and H*=I.
-/
#check @krylov.Functions.existsUnique_local_chord_minimum
#check @krylov.Functions.exact_gradient_search

/-!
Article: Lemma E.3 [lem:rorder2]. R-order of secant recursions.

Delayed product and corrected recurrences imply the actual exponential-barrier R-order, with no rate assumed as a record field.

The root definition matches the two delayed indices; zero errors, stationary tails and finite-prefix shifts are handled in the formal recurrence theorems.
-/
#check @krylov.Convergence.rorder_product_recurrence
#check @krylov.Convergence.rorder_corrected_recurrence

/-!
Article: Lemma E.4 [apG:restart]. Gradient at a non-descent direction or a short step.

For the real observed FC direction, non-descent and short steps give the exact 2(1+√κ) and 4κ gradient bounds.

The physical wrapper uses ratio²=κ and the canonical step norm ‖H_*^{1/2}d‖, matching the corrected article.
-/
#check @krylov.Correction.windowDirection_sharp_nondescent
#check @krylov.Correction.windowDirection_sharp_short_step

/-!
Article: Lemma E.5 [lem:cycle-transfer]. From a finite cycle to a function.

The generic homogeneous substitution theorem produces degree d+1 from a degree-d operator response. Native finite FC/RFC scalar executors supply localized queries and genuine tensor jets.

The operator polynomial and its remainder are hypotheses of this transfer lemma, exactly as in the article; localization and reference-replacement estimates are separately derived from actual searches.
-/
#check @krylov.Functions.homogeneous_cycle_transfer
#check @krylov.Functions.homogeneous_cycle_transfer_quadratic
#check @krylov.Functions.metricFCPoint_homogeneous_transfer
#check @krylov.Functions.nativeRFCPoint_homogeneous_transfer

/-!
Article: Proposition E.7 [thm:Htransfer]. Compatible function increments.

Actual FC/RFC query secants have compatible slices of the same genuine scalar third derivative; the resulting spatial response degrees are two and three.

C3 supplies a compact-uniform little-o remainder; Lipschitz D3 yields the next-power remainder. Canonical and physical metrics are related by the explicit metric coordinates.
-/
#check @krylov.Functions.metricFCPoint_leading_gradient
#check @krylov.Functions.nativeRFC_tensor_cubic_remainder
#check @krylov.Functions.nativeRFC_tensor_quartic_remainder

/-!
Article: Proposition E.8 [thm:Hp]. Tensor amplification.

The computed CG frame has an attained symmetric cubic spectral/nuclear dual coefficient, a genuine lower witness and the printed independent-operator upper bounds.

The tensor-product norm in the formal dual is the proved projective/nuclear norm; the lower energy factor uses the true canonical CG step length √c0.
-/
#check @krylov.Tensor.reference_cubic_amplification_bounds

/-!
Article: Theorem E.9 [thm:H]. Cubic realization of the lower bound.

The actual harmonic cubic is self-concordant on the printed metric ball, realizes RFC’s leading half coefficient and budgets, and has the complete planar minimax lower/RFC upper inequalities.

The competing method is quantified after the common small source radius. The native spatial leading value, own-base normalization and compatible tensor restrictions are derived, not supplied.
-/
#check @krylov.Functions.metricCubic_selfConcordant_radius
#check @krylov.Functions.harmonic_nativeRFC_realization
#check @krylov.Functions.native_harmonic_total_budget
#check @krylov.Functions.native_harmonic_correction_budget
#check @krylov.Information.binaryPlanarMinimax_bounds

/-!
Article: Proposition E.10 [thm:struct]. Gradient-indistinguishable cubics.

Genuine smooth hidden cubics preserve the full sampled vector-gradient transcript, latest model and zero observed defect while changing the final compression by the stated rank-one term; the oldest value defect equals −c/12.

The scalar bilinear differential is transported to the actual Riesz gradient in quadraticHidden_gradient_transcript/vector_secant.
-/
#check @krylov.Functions.quadraticHidden_gradient_transcript
#check @krylov.Functions.quadraticHidden_model
#check @krylov.Functions.quadraticHidden_final_compression
#check @krylov.Functions.quadraticHidden_oldest_defect

/-!
Article: Lemma E.11 [apA:lem:angle]. The family of Proposition~\ref{thm:struct}.

The entire hidden increment sequence has the stated rank-one form, and affine Hessians give the exact midpoint contraction and normalized absolute cosine.

The divided identity requires nonzero cubic coefficient and midpoint displacement; the undivided identity covers zero cases.
-/
#check @krylov.Functions.hidden_first_increment
#check @krylov.Functions.hidden_interior_increment
#check @krylov.Functions.hidden_final_increment
#check @krylov.Functions.affine_secant_diagonal_bound
#check @krylov.Functions.hidden_normalized_cosine

/-!
Article: Proposition E.12 [apG:flat]. Flat profile.

The actual equal-energy CG profile has the printed tensor lower/upper bounds and exact independent-operator square-root sum with its integral lower estimate.

The factor c is an actual positive common CG energy under the nonexhausted n≥2 reference hypothesis.
-/
#check @krylov.Tensor.reference_flat_tensor_amplification
#check @krylov.Tensor.reference_flat_operator_eq
#check @krylov.Tensor.reference_flat_operator_lower

/-!
Article: Lemma E.13 [thm:Fexact]. Trapezoid remainder.

The true scalar-function trapezoid remainder has exactly the printed constants for every anchor/split. The diagonal fourth-derivative version and cubic exactness use genuine derivatives.

The diagonal spectral norm of the scalar symmetric tensor is converted to the needed mixed bound by the proved Banach identity; the convex segment/anchor domain is retained.
-/
#check @krylov.Functions.anchored_trapezoid_remainder
#check @krylov.Functions.anchored_trapezoid_remainder_fourthDiagonal
#check @krylov.Functions.cubicPolynomial_corrected_diagonal

/-!
Article: Theorem E.14 [thm:D]. Restarted cycles.

Actual restarted scalar FC/RFC executors have the printed sharp true-Hessian error constants and C3 little-o recurrences.

The literal observed compact normalized-reference condition is retained; convergence of cycle-start errors is a hypothesis, rather than inferred from the formal asymptotic inequality alone.
-/
#check @krylov.Convergence.restarted_nativeFC_C3_sharp_error
#check @krylov.Convergence.restarted_nativeRFC_C3_sharp_error

/-!
Article: Theorem E.15 [thm:V]. Virtual-launch expansion.

Genuine scalar virtual-launch execution gives the midpoint tensor coefficient and bound; near-exact reference trials yield cubic improvement, in both retained bases.

Primitive positive homogeneous C2 trial charts and compact nondegenerate reference directions implement V1–V3. The claimed gradient is the actual gradient at the unevaluated virtual point.
-/
#check @krylov.Convergence.xrfcFunction_C3_tensor_leading_gradient
#check @krylov.Convergence.xrfcTensorCoefficient_norm_bound
#check @krylov.Convergence.xrfcFunction_near_exact_original_C3_cubic

/-!
Article: Theorem E.16 [thm:LB]. One-gradient lower bound on cubic functions.

Actual gradient-indistinguishable cubic twins give the arbitrary-method spectral/fixed-fibre lower bound in the true minimizer metric; the native XRFC policy attains its leading coefficient.

The formal auxiliary loss parameter is specialized to δ/10 so its tensor and metric factors imply the exact printed 1±δ allowances. The genuine local minimum and true Hessian spectrum are constructed.
-/
#check @krylov.Convergence.oneGradient_spectral_true_lower
#check @krylov.Convergence.oneGradient_fixed_fibre_true_lower
#check @krylov.Convergence.oneGradient_true_lower_loss
#check @krylov.Convergence.xrfcBasis_cubic_actual_attainment

/-!
Article: Proposition E.17 [apG:Dunif]. Uniform orders with restart rules.

The literal observable restarting FC/RFC cycles satisfy the stated n^{3/2} quadratic/cubic bounds on genuine self-concordant objectives, with an absolute constant and a radius depending only on n,κ and the cutoff.

Undefined/non-descent stops, stationary points, failed energy gates, value acceptance and proper domains containing the fixed canonical ball are all covered; no independence condition is assumed.
-/
#check @krylov.Convergence.observable_fc_true_kappa_domain_uniform
#check @krylov.Convergence.observable_rfc_true_kappa_domain_uniform

/-!
Article: Proposition E.18 [thm:G]. Sliding full conjugacy.

The physical sliding executor supplies automatic asymptotic orthogonality/conditioning; the exact delayed product, R-order and conditional sharp half coefficient follow.

Canonical centering changes only coordinates, not the observed direction. The half coefficient retains the additional Q-superlinearity assumption; no independent-window condition is added.
-/
#check @krylov.Convergence.source_path_sharp_product
#check @krylov.Convergence.source_path_rorder
#check @krylov.Convergence.source_path_half_product
#check @krylov.Convergence.metricSlidingFCSequence_source_data

/-!
Article: Theorem E.19 [thm:Ip]. Secant steps and the age of a window.

Actual SS1 and ordinary sliding RFC have the stored-only oldest-distance sharp product coefficient, superlinearity and characteristic-root order, with the correct physical metrics and gradient clock.

The eventual gate conclusion concerns ordinary RFC’s canonical defect gate, not an unrelated fixed spectral threshold. The latter requires its own quantitative hypothesis.
-/
#check @krylov.Convergence.ss1Sequence_printed_oldest_bound
#check @krylov.Convergence.ss1Sequence_physical_rorder
#check @krylov.Convergence.rfcPath_printed_oldest_bound
#check @krylov.Convergence.slidingRFCSequence_superlinear
#check @krylov.Convergence.rfcPath_rorder

/-!
Article: Lemma E.20 [lem:ss1-local]. Local SS1 convergence; {\cite{Burdakov83}}.

Starting sufficiently near the nondegenerate minimum, the genuine physical SS1 sequence with the original Euclidean determinant bound either terminates or converges with the asserted R-order.

The hypothesis is on every nonstationary window; the theorem explicitly includes stationary termination and derives metric-window inverse bounds from the original determinant.
-/
#check @krylov.Convergence.ss1_local_original_physical_convergence

/-!
Article: Theorem F.1 [thm:metric]. The relative metric.

Threshold coincidence on all residuals or a nonempty open set is equivalent to proportional metrics. The physical relative correction has the exact minimax value and complete subcritical/critical/supercritical minimizer sets.

The formal coefficient vector is the actual window correction; the uncertainty interval is exactly the relative-norm budget. The zero residual and empty dimension are included.
-/
#check @krylov.XR.metric_thresholds_open_iff
#check @krylov.XR.metric_thresholds_all_iff
#check @krylov.XR.metric_threshold_common_value
#check @krylov.XR.relativeCorrection_isLeast
#check @krylov.XR.relativeCorrection_small_iff
#check @krylov.XR.relativeCorrection_large_iff
#check @krylov.XR.relativeCorrection_critical_iff
#check @krylov.XR.relativeCorrection_uncertainty

/-!
Article: Proposition F.2 [prop:cert]. Hereditary window test.

The real-model/skew-norm test is equivalent to actual complex Hermitian positivity, inherited by ordered restrictions. Reversed Cholesky produces exactly the longest positive chronological suffix.

The generic empty suffix is allowed; actual stored positive secants ensure the one-pair suffix and justify the clamp in the printed algorithm.
-/
#check @krylov.XR.windowUnrefuted_iff
#check @krylov.XR.windowUnrefuted_submatrix
#check @krylov.XR.unrefutedSuffix_spec
#check @krylov.XR.unrefutedSuffix_minimal
#check @krylov.XR.unrefutedSuffixByCholesky_eq

/-!
Article: Proposition F.3 [prop:cond]. With a known budget the defect sharpens the worst case.

The true known-base and compressed-data fibres have exact attained conditional radii; actual two-dimensional physical histories realize them.

Feasibility ellipses, strict defect monotonicity, zero-defect/zero-budget cases and the equality branch δ=0 are retained by the underlying conditional modules.
-/
#check @krylov.XR.knownConditionalFibre
#check @krylov.XR.unknownConditionalFibre
#check @krylov.XR.conditionalPhysical_model_radius

/-!
Article: Proposition F.4 [prop:status]. Variation certified by refutation.

Actual physical flag bounds imply the exact general/conjugate retention and refutation thresholds, together with the hidden-error radius and minimax consequence.

The budget bounds entering VariationThreshold are derived in FlagVariation/PhysicalVariation; their availability is not an extra article assumption.
-/
#check @krylov.XR.variation_budget_retention
#check @krylov.XR.variation_budget_refutation
#check @krylov.XR.conjugate_budget_retention
#check @krylov.XR.conjugate_budget_refutation
#check @krylov.XR.retained_full_correction_minimax

/-!
Article: Lemma F.5 [apH:canon]. Canonical defect.

The canonical normalization preserves the actual relative norm, and the two operator-norm estimates yield exactly the extreme-eigenvalue comparison. The two-pair formula has determinant denominator.

For an SPD model, operator norm is λmax and inverse operator norm is 1/λmin; these equivalent spectral forms explain the printed bounds. Comparability does not assert identical gate decisions.
-/
#check @krylov.XR.canonical_relativeBudget
#check @krylov.XR.canonical_defect_bounds
#check @krylov.XR.canonical_two_pair_formula

/-!
Article: Lemma F.6 [lem:mm]. Model step.

Raw model normal solves give a unique physical block-quadratic minimizer and the exact slope/energy and quadratic directional identities. The actual Taylor quotient is at unit trial.

The physical minimizer and gᵀd=ĝᵀd need nonsingular conjugacy and an independent augmented frame. The scalar slope identity alone is more general. Safeguarded replacement is excluded from the model-minimizer interpretation. The divided trial quotient is used at nonstationary anchors.
-/
#check @krylov.XR.modelDirection_conjugate
#check @krylov.XR.modelDirection_slope
#check @krylov.XR.modelTrialStep_slope
#check @krylov.XR.physicalBlockModel_minimizer
#check @krylov.XR.modelTrial_quadratic_curvature
#check @krylov.XR.trialQuotient_model_energy

/-!
Article: Lemma F.7 [lem:anchor]. Anchor invariance.

Virtual point/gradient, direction, length and physical trial point are unchanged by the last-pair anchor shift; the displacement itself changes by minus the last step.

The virtual solve requires an invertible latest model and the trial-length step also uses invertible conjugacy.
-/
#check @krylov.XR.modelVirtualPoint_anchor
#check @krylov.XR.modelVirtualGradient_anchor
#check @krylov.XR.modelDirection_anchor
#check @krylov.XR.modelTrialLength_anchor
#check @krylov.XR.modelTrialPoint_anchor

/-!
Article: Lemma F.8 [apG:local]. The model step near a nondegenerate minimizer.

Primitive normalized secant errors and independence derive actual inverse/model/Hermitian domains, slope and norm bounds, and the true weighted Taylor quotient.

Constants are uniform over p≤n. In a full window the missing direction vanishes and its ℓ,Λ parameters are unnecessary, as in the corrected G4 and lemma conclusion.
-/
#check @krylov.XR.local_raw_window_domains
#check @krylov.XR.local_raw_windowUnrefuted
#check @krylov.XR.dimension_model_step_gradientRelated
#check @krylov.XR.primitive_local_model_quotient
#check @krylov.XR.modelDirection_zero_full_window

/-!
Article: Proposition F.9 [apG:radau-adequate]. The Gauss--Radau trial is adequate.

A strict spectral band and small genuine secant errors imply all actual Schur inverse domains and the midpoint adequacy ratio, uniformly over window sizes.

The raw physical-source theorem is stronger than the printed O(ε) estimate: it constructs a feasible compression preserving the true directional curvature. The Armijo restriction remains explicit.
-/
#check @krylov.XR.rawWindow_radau_adequate
#check @krylov.XR.radau_uniform_radius

/-!
Article: Proposition F.10 [prop:floor]. Adequacy floor.

The literal spectral curvature with its upper-only floor satisfies G3 under true local source conditions and a strict upper spectral margin; quadratic upper clipping cannot increase trial error.

This is a property of the spectral policy. The secant policy uses G3 as a hypothesis and does not inherit this floor guarantee.
-/
#check @krylov.XR.algorithmComputedCurvature_uniform_floor_radius
#check @krylov.XR.algorithmComputedCurvature_fixed_prior_floor_radius
#check @krylov.XR.rawQuadratic_upper_clip_trial_error

/-!
Article: Lemma F.11 [lem:xr-local]. Local equivalence with XRFC.

Strict finite quadratic decisions persist for actual nearby scalar objectives; literal full-memory XR/XR-F outputs agree with the corresponding scalar virtual executors. Actual operator trial vectors give the first variation and quadratic trial-rule comparison.

The positive C2 policy chart is an explicit hypothesis. Simple extreme Ritz values are needed only for the spectral chart; primitive smooth trial policies, including the secant scale, use the general prescribed-trial transfer.
-/
#check @krylov.XR.native_XR_local_XRFC_outputs
#check @krylov.XR.nativeOperatorOutput_actual_gradient
#check @krylov.XR.c2_reference_trial_comparison_bigO
#check @krylov.XR.prescribedXRFC_regular_trial_transfer
