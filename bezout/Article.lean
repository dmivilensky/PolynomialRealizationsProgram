import bezout

/-!
Article: bezout — complete ordered mathematical signatures.
Use: ArticleMap.md records hypotheses, normalization, physical execution semantics
and the symbolic scope of every numbered and significant unnumbered claim.
Proof trust: Check.lean audits every owned source and transitive proof dependency.
-/

/-!
Article: Theorem 2.1 [thm:bezout]. Realization identity.
Arbitrary real strictly causal coefficients and arbitrary memory; actual execution in every real module; exact nominal queries and physical additive response. Full terminal degree forces both exact degree orders. The divided difference includes its derivative diagonal and is jointly continuous. The actual Chebyshev-exact histories are in bijection with all eta-normalized graded query families, and the response factors are unique. The article assumes N>=2; the classification is proved already for N>0.
-/
#check @bezout.History.run
#check @bezout.History.execution_unique
#check @bezout.History.nominal_query
#check @bezout.History.physical_response
#check @bezout.History.nominal_output
#check @bezout.realization_identity
#check @bezout.realizationEquiv
#check @bezout.NormalizedFamily.existsUnique_history
#check @bezout.GradedFamily.existsUnique_realization
#check @bezout.History.chart_factors_unique
#check @bezout.History.chartQuery_physical_eval
#check @bezout.History.chartFactor_physical_eval
#check @bezout.History.realization_residualPolynomial
#check @bezout.History.realization_kernel
#check @bezout.History.realization_operatorTransfer
#check @bezout.History.chebyshevExact_iff_scalar_terminal
#check @bezout.History.chebyshevExact_iff_noiseless_scalar_run
#check @bezout.History.chebyshevExact_noiseless_output
#check @bezout.Properties.terminal_minimax
#check @bezout.Properties.terminal_minimax_attained
#check @bezout.History.oracleOutput_map
#check @bezout.History.oracleOutput_isometry
#check @bezout.History.oracleOutput_mse_isometry

/-!
Article: Theorem 3.1 [thm:additive]. Exact additive optima.
Every N>=2 and strict positive spectral interval; r,t>=0, and arbitrary real sigma (hence all nonnegative variance budgets). Risks equal literal suprema over all finite real Hilbert spaces, admissible symmetric Hessians and actual executions. The stochastic class has conditional centering and conditional second moment at most sigma squared, with deterministic Hessian and initial state; independence is required only by the explicit attaining sign model. The same constructed Flat history attains both exact IsLeast minima. Its independently prepared four-register program has identical actual queries and output for every time-dependent oracle and exactly N calls.
-/
#check @bezout.Flat.history_exact
#check @bezout.Flat.response_uniform_sharp
#check @bezout.Risk.additiveRisk_eq_sSup
#check @bezout.Risk.mseRisk_eq_sSup
#check @bezout.Risk.scalar_additive_attainment
#check @bezout.Risk.scalar_mse_attainment
#check @bezout.Probability.Signs.martingale
#check @bezout.Probability.Signs.conditional_variance
#check @bezout.Flat.additiveRisk_eq
#check @bezout.Flat.mseRisk_eq
#check @bezout.Flat.additive_minimum
#check @bezout.Flat.mse_minimum
#check @bezout.Algorithms.Flat.preparedProgram_eq
#check @bezout.Algorithms.Flat.scalarProgram_correct
#check @bezout.Algorithms.Flat.scalarProgram_cost_le
#check @bezout.Algorithms.Flat.scalarProgram_storage_le
#check @bezout.Algorithms.Flat.scalarProgram_defined
#check @bezout.Algorithms.Flat.cachedProgram_output_eq_history
#check @bezout.Algorithms.Flat.query_eq_history
#check @bezout.Algorithms.Flat.prepared_output_eq_history
#check @bezout.Algorithms.Flat.physical_response
#check @bezout.Algorithms.Flat.affineOracle_output
#check @bezout.Algorithms.Flat.oracle_calls
#check @bezout.Algorithms.Flat.vector_slots
#check @bezout.Classical.variance_exact
#check @bezout.Classical.mseRisk_eq
#check @bezout.Classical.additiveRisk_eq
#check @bezout.Classical.variance_eq_tsum
#check @bezout.Classical.variance_tendsto
#check @bezout.Classical.varianceLimit_pos

/-!
Article: Theorem 4.1 [thm:linear]. Linear energy optimum.
All N>=2, including the exact odd-horizon correction, with arbitrary real causal competing histories and arbitrary memory. The insertion sum is the derivative of actual perturbed oracle execution. Spectral, temporal operator-norm and local actual-query relative gains have the stated universal lower bounds; both arbitrary and symmetric Hilbert--Schmidt and operator perturbation classes have the same attained optimum. The local gain equals the literal positive-scale limsup of worst-case normalized deviations for every radius r>0; its quadratic remainder is uniform in dimension and adaptive errors. One explicit positive parity construction attains all minima. Independently prepared impulses and reverse readout scalars implement its six-register actual program with exactly N calls.
-/
#check @bezout.History.hasDerivAt_perturbed_output
#check @bezout.History.matrixResponse_action
#check @bezout.History.hasDerivAt_matrix_output
#check @bezout.History.matrixResponse_eq_realization
#check @bezout.History.hs_matrixResponse_bound
#check @bezout.History.matrixResponse_opNorm_le
#check @bezout.History.linearGain_le_spectralGain
#check @bezout.Gains.linearGain_le_operatorGain
#check @bezout.Gains.linearGain_le_localRelativeGain
#check @bezout.Gains.linearGain_le_hsGain
#check @bezout.Analysis.relative_response_bound
#check @bezout.Gains.localRelativeGain_eq_limsup
#check @bezout.Gains.localRelativeGain_eq_limsup_sSup
#check @bezout.Gains.localRelativeGain_eq_radius_limsup
#check @bezout.Balanced.history_exact
#check @bezout.Balanced.bound_energy
#check @bezout.Properties.linearCorrection_sub_one_isBigO
#check @bezout.Balanced.linear_optima
#check @bezout.Balanced.spectral_minimum
#check @bezout.Balanced.operator_minimum
#check @bezout.Balanced.local_relative_minimum
#check @bezout.Balanced.hs_minimum
#check @bezout.Algorithms.Balanced.preparedImpulse_eq
#check @bezout.Algorithms.Balanced.preparedReadout_eq
#check @bezout.Algorithms.Balanced.prepare_cost_le
#check @bezout.Algorithms.Balanced.prepare_storage_le
#check @bezout.Algorithms.Balanced.normalizationProgram_defined
#check @bezout.Algorithms.Balanced.cachedProgram_output_eq_history
#check @bezout.Algorithms.Balanced.prediction_register
#check @bezout.Algorithms.Balanced.query_eq_history
#check @bezout.Algorithms.Balanced.physical_response
#check @bezout.Algorithms.Balanced.affineOracle_output
#check @bezout.Algorithms.Balanced.oracle_calls
#check @bezout.Algorithms.Balanced.vector_slots
#check @bezout.Classical.spectralGain_exact
#check @bezout.Classical.operatorGain_eq
#check @bezout.Classical.localRelativeGain_eq
#check @bezout.Classical.gain_asymptotic
#check @bezout.Comparisons.Competitors.Sine.gain_ratio_balanced_sq
#check @bezout.Comparisons.Competitors.Sine.gain_ratio_sq_limit
#check @bezout.Comparisons.Competitors.Sine.gain_eventually_lt_prefix
#check @bezout.Balanced.one_le_psi_eval
#check @bezout.Balanced.actualRawQuery_expansion
#check @bezout.Balanced.actualRawQuery_fourth_order
#check @bezout.Balanced.actualRawQuery_one
#check @bezout.Balanced.actualAuxiliary_one
#check @bezout.Balanced.actualAuxiliary_two
#check @bezout.Balanced.actualAuxiliary_first_step
#check @bezout.Balanced.actualAuxiliary_recurrence
#check @bezout.Balanced.actualRawQuery_auxiliary_step

/-!
Article: Lemma C.1 [lem:two-masses]. Separation of two masses.
All odd N>=3 and arbitrary finite temporal index types of cardinality N. Both real signed and nonnegative energies have the stated attained minimum, with explicit disjoint pure support witnesses. The proof replaces the manuscript optimizer/KKT argument by exact pointwise supporting quadratics and integer cone counts, including the small odd horizons. The normalization N^3 sigma_N^2/4 and the displayed A^2/m+B^2/(N-m) value are proved equal.
-/
#check @bezout.Lower.signed_mass_separation
#check @bezout.Lower.nonnegative_mass_separation
#check @bezout.Lower.signed_mass_minimum
#check @bezout.Lower.nonnegative_mass_minimum
#check @bezout.Lower.exists_pure_mass_attainment
#check @bezout.Lower.mass_value_quotient
#check @bezout.Lower.oddEnergy_eq_correction

/-!
Article: Lemma C.2 [lem:four-corners]. Four-corner bound.
Every real separated factorization of the actual odd Chebyshev Bezoutian, with no degree, sign or normalization restrictions. Both the ordinary four-corner energy and the stronger symmetrized cross-corner energy are bounded from below. The results are instantiated for actual causal histories and transported to physical coordinates with the exact 4 epsilon/Delta scale. Symmetrization retains the coupling needed by symmetric Hilbert–Schmidt perturbations.
-/
#check @bezout.Lower.symmetric_four_corner_lower_normalized
#check @bezout.Lower.four_corner_lower_normalized
#check @bezout.Lower.chebyshev_symmetric_four_corner_lower
#check @bezout.Lower.chebyshev_four_corner_lower
#check @bezout.Lower.history_chart_symmetric_four_corner_lower
#check @bezout.Lower.history_physical_symmetric_four_corner_lower
#check @bezout.Lower.history_physical_four_corner_lower

/-!
Article: Proposition D.1 [prop:experiment-order]. Root ordering in the commuting channel model.
Every permutation of explicitly constructed reciprocal affine Chebyshev roots, with the literal dyadic interlacing permutation as a specialization. The actual physical diagonal kernel is the omitted-factor polynomial and, away from its removed root, the displayed quotient; the polynomial supplies the continuous extension at roots. Column reindexing preserves the actual Euclidean operator norm and full HS energy. Paired commuting products and an actual iid product probability law give finite terminal-distribution invariance and the exact product variance, without a small-noise assumption. The exact quartic endpoint energies and even cross correlation are proved, as are uniform fixed-interior quadratic bounds. For arbitrary finite fixed strict interior spectra and equal positive endpoint masses, the literal LF/Prefix operator and squared-HS ratios are asymptotic to sqrt(N)/2 and N/2 along dyadic horizons; stronger limit versions allow any divergent even sequence and arbitrary root orders. Physical epsilon/Delta factors cancel at every chart point, including roots. Supporting Appendix D signatures also retain each competitor own finite terminal, full finite-sign oracle execution, actual covariance and symbolic generalizations of the experimental models.
-/
#check @bezout.Channel.Roots.doublePermutation_interlace
#check @bezout.Channel.Roots.dyadicPermutation_bijective
#check @bezout.Channel.Roots.steps_pos
#check @bezout.Channel.Roots.terminal_steps_eq
#check @bezout.Comparisons.Competitors.LF.terminal
#check @bezout.Comparisons.Competitors.LF.output_eq_history
#check @bezout.Channel.Roots.history_exact
#check @bezout.Channel.Roots.lfHistory_exact
#check @bezout.Channel.Roots.history_diagonalKernel
#check @bezout.Channel.Roots.history_root_quotient
#check @bezout.Channel.Roots.history_endpointEnergy_mu
#check @bezout.Channel.Roots.history_endpointEnergy_L
#check @bezout.Channel.Roots.history_endpointCross
#check @bezout.Channel.Roots.continuous_diagonalProfile
#check @bezout.Channel.Roots.signalNorm_permute
#check @bezout.Channel.Roots.signalHsSq_permute
#check @bezout.Channel.Roots.normalized_signalMatrix
#check @bezout.Channel.Roots.signalNorm_ratio_interval
#check @bezout.Channel.Roots.signalHsSq_ratio_interval
#check @bezout.Channel.Roots.history_mode_product
#check @bezout.Channel.Roots.history_mode_paired_permute
#check @bezout.Channel.Roots.terminal_distribution_iid
#check @bezout.Channel.Roots.euclidean_mode_product
#check @bezout.Channel.Roots.euclidean_mode_variance
#check @bezout.Channel.Roots.chebyshev_interior_energy_le
#check @bezout.Channel.Roots.diagonalEnergy_interior_le
#check @bezout.Comparisons.RootAsymptotics.matrix_normalized_limits
#check @bezout.Comparisons.RootAsymptotics.operator_ratio_limit
#check @bezout.Comparisons.RootAsymptotics.hs_ratio_limit
#check @bezout.Comparisons.RootAsymptotics.lf_operator_isEquivalent
#check @bezout.Comparisons.RootAsymptotics.lf_hs_isEquivalent
#check @bezout.Models.Network.projector_idempotent
#check @bezout.Models.Network.hessian_antisymmetric
#check @bezout.Models.Network.eigenmode
#check @bezout.Models.Network.chart_cancellation
#check @bezout.Models.Network.channel_block_action
#check @bezout.Models.Network.channel_weight_pos
#check @bezout.Models.Network.cycle_diagonalization
#check @bezout.Models.Network.activeEmbedding_norm_sq
#check @bezout.Models.Network.ambientOracle_embedding
#check @bezout.Models.Network.network_output_active
#check @bezout.Models.Network.network_mse_active
#check @bezout.Comparisons.Competitors.Momentum.terminal_eval
#check @bezout.Comparisons.Competitors.Momentum.response_eval
#check @bezout.Comparisons.Competitors.DFB.terminal_eval
#check @bezout.Comparisons.Competitors.DFB.response_eval
#check @bezout.Comparisons.Competitors.DFB.physical_response
#check @bezout.Comparisons.Competitors.DFB.integral_output_common_covariance
#check @bezout.Comparisons.Competitors.MASG.truncated_last_stage
#check @bezout.Comparisons.Competitors.MASG.query_at_reset
#check @bezout.Comparisons.Competitors.MASG.oracle_calls
#check @bezout.Comparisons.Competitors.MASG.output_eq_history
#check @bezout.Comparisons.Competitors.MASG.response_eval
#check @bezout.History.integral_stochasticOutput_covariance
#check @bezout.History.integral_stochasticOutput_common_covariance
#check @bezout.History.integral_stochasticOutput_spectral_covariance
#check @bezout.History.integral_stochasticOutput_rankOne
#check @bezout.Models.Ridge.root_square
#check @bezout.Models.Ridge.root_inverse
#check @bezout.Models.Ridge.design_identities
#check @bezout.Models.Ridge.design_gradient
#check @bezout.Models.Ridge.design_average_minimizer
#check @bezout.Probability.Dither.normalizedError_preserving
#check @bezout.Probability.Dither.quantizer_error
#check @bezout.Probability.Dither.quantizer_unbiased
#check @bezout.Probability.Dither.quantizer_variance
#check @bezout.Probability.Dither.fresh_preserving
#check @bezout.Probability.Dither.fresh_independent
#check @bezout.Probability.Dither.fresh_conditional_mean
#check @bezout.Probability.Dither.fresh_conditional_square
#check @bezout.Channel.hasDerivAt_signal_output
#check @bezout.Channel.signalOperator_sharp
#check @bezout.Channel.finiteNoise_expansion
#check @bezout.Channel.finiteNoiseCoefficient_empty
#check @bezout.Channel.finiteNoiseCoefficient_singleton
#check @bezout.Channel.finiteSignOutput_mean
#check @bezout.Channel.finiteSignOutput_variance
#check @bezout.Channel.finiteNoiseRemainder_nonneg
#check @bezout.Channel.finiteNoiseRemainder_isBigO
#check @bezout.Channel.signal_endpoint_mass_bounds
#check @bezout.Probability.Dither.workerError_eq
#check @bezout.Probability.Dither.fresh_worker_preserving
#check @bezout.Probability.Dither.workerError_conditional_mean
#check @bezout.Probability.Dither.workerError_covariance
#check @bezout.Probability.Dither.workerError_normalized_covariance
#check @bezout.Probability.Dither.workerError_normalized_conditional_norm_sq
#check @bezout.Probability.Dither.workerError_normalized_conditional_cross
#check @bezout.Channel.finiteNoiseCoefficient_signal_column
#check @bezout.Channel.finiteSignOutput_signal_variance
#check @bezout.Channel.finiteSignOutput_norm_sq
#check @bezout.Channel.prefix_signal_endpoint_mass_bounds
#check @bezout.Channel.sine_signal_endpoint_mass_bounds
#check @bezout.Channel.balanced_signal_endpoint_mass_bounds
#check @bezout.Channel.sine_balanced_variance_ratio_ge
#check @bezout.Channel.sineBalancedVarianceLower_tendsto
#check @bezout.Channel.sine_balanced_variance_separation
#check @bezout.Channel.additiveOperator_physical
#check @bezout.Channel.stackedNoise_energy
#check @bezout.Channel.additiveMaxProfile_unit
#check @bezout.Channel.additiveMaxProfile_action
#check @bezout.Channel.additiveOperator_norm
#check @bezout.Channel.additive_physical_sharp
#check @bezout.Models.Network.cycleEigenvalue_strict
#check @bezout.Models.Network.realEigenbasis_diagonalization
#check @bezout.Models.Network.realEigenvalue_strict
#check @bezout.Models.Network.cycleFiniteSignal
#check @bezout.Models.Network.cycle_network_output_spectral
#check @bezout.Models.Network.cycle_network_hasDerivAt
#check @bezout.Models.Network.cycle_network_mse_spectral
#check @bezout.Models.Network.cycle_network_root_variance
#check @bezout.Channel.additive_physical_spectral_coordinates
#check @bezout.Channel.spectralAdditiveEnergyMax_spectrum
#check @bezout.Channel.additive_physical_sharp_selfAdjoint
#check @bezout.Models.Ridge.exists_basis_with_unit
#check @bezout.Models.Ridge.spectralMap_coordinates
#check @bezout.Models.Ridge.run_coordinates
#check @bezout.Models.Ridge.integral_stochasticOutput_rankOne
#check @bezout.Models.Network.cycle_network_root_distribution_permute
#check @bezout.Models.Network.cycle_network_derivative_norm
#check @bezout.Models.Network.cycle_lf_operator_isEquivalent
#check @bezout.Models.Network.cycle_lf_hs_isEquivalent
#check @bezout.Probability.covariance_isotropic_inner
#check @bezout.Models.Ridge.integral_stochasticOutput_rankOne_covariance
#check @bezout.Probability.Dither.Temporal.stagePair_preserving
#check @bezout.Probability.Dither.Temporal.temporal_martingale
#check @bezout.Probability.Dither.Temporal.error_covariance
#check @bezout.Probability.Dither.Temporal.error_conditional_cross
#check @bezout.Probability.Dither.Temporal.error_conditional_norm_sq
#check @bezout.Probability.Dither.quantizedQuery_truncate
#check @bezout.Probability.Dither.quantizedOutput_eq_run
#check @bezout.Probability.Dither.quantizedOutput_eq_stochastic
#check @bezout.Probability.Dither.quantizedStream_martingale
#check @bezout.Probability.Dither.quantizedStream_covariance
#check @bezout.Probability.Dither.integral_quantizedOutput_covariance
#check @bezout.Probability.Dither.integral_quantizedOutput_rankOne
