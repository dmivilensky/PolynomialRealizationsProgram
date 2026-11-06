import chebyshev1

/-!
Manually reviewed signatures for the 34 numbered main and supplementary
statements. ArticleMap.md records exact hypotheses and interpretation;
ArticleAudit.md records the proof and subsequent correspondence reviews.
-/

/-! Article: Definition 3.1 [def:realization]. Realization. -/
#check @chebyshev1.Realization
#check @chebyshev1.Realization.scalarStep
#check @chebyshev1.Realization.operatorTransfer
#check @chebyshev1.Realization.residualPolynomial
#check @chebyshev1.Realization.Normalized
#check @chebyshev1.Realization.normalized_iff_scalarTransfer_zero
#check @chebyshev1.Realization.AffineConsistent
#check @chebyshev1.Realization.physicalMemory
#check @chebyshev1.Realization.physicalOutput_error
#check @chebyshev1.Realization.physicalOutput_quadratic_error
#check @chebyshev1.Realization.AffineConsistent.center_eq_product
#check @chebyshev1.Realization.AffineConsistent.residual_zero
#check @chebyshev1.TwoTerm.affineConsistency
#check @chebyshev1.Stepsize.affineConsistency
#check @chebyshev1.JacobiData.affineConsistency
#check @chebyshev1.Prefix.affineConsistency
#check @chebyshev1.Realization.residualPolynomial_natDegree_le
#check @chebyshev1.Realization.residual_minimax_lower
#check @chebyshev1.TwoTerm.nonlinearError_translate_upto
#check @chebyshev1.Nonlinear.errorTrajectory_translate

/-! Article: Definition 3.2 [def:kernel]. First-order kernel. -/
#check @chebyshev1.Realization.kernel
#check @chebyshev1.Realization.kernelNorm
#check @chebyshev1.Realization.gain

/-! Article: Lemma 3.1 [lem:first-order-expansion]. First-order expansion. -/
#check @chebyshev1.Realization.hasDerivAt_operatorTransfer
#check @chebyshev1.Realization.linearResponse_eq_sum
#check @chebyshev1.Realization.spectralPair_linearResponse
#check @chebyshev1.Realization.linearResponse_coordinates

/-! Article: Proposition 3.1 [prop:finite-drift-linear]. Finite drift and the size of the linear response. -/
#check @chebyshev1.orderedProduct_add_expansion
#check @chebyshev1.insertionMultilinear
#check @chebyshev1.Realization.finiteDrift_polynomial_decomposition
#check @chebyshev1.Realization.operatorTransfer_affine_by_degree
#check @chebyshev1.Realization.hsNorm_linearResponse_bound
#check @chebyshev1.Realization.hs_bound_attained
#check @chebyshev1.Realization.hs_constant_minimal
#check @chebyshev1.Realization.gain_attained
#check @chebyshev1.Realization.linearResponse_eq_sum_of_kernel_factorization
#check @chebyshev1.Realization.opNorm_linearResponse_le_gain_l2_of_kernel_factorization
#check @chebyshev1.JacobiData.opNorm_linearResponse_le_gain_l2
#check @chebyshev1.Prefix.opNorm_linearResponse_le_gain_l2
#check @chebyshev1.SineJacobi.opNorm_linearResponse_le_gain_l2

/-! Article: Theorem 3.1 [thm:stepsize-lower]. Drift gain of exact stepsize schedules. -/
#check @chebyshev1.Stepsize.endpoint_square_sum
#check @chebyshev1.Stepsize.gain_lower_bound
#check @chebyshev1.Stepsize.correction_error_isBigO
#check @chebyshev1.Stepsize.lowerBound_asymptotic
#check @chebyshev1.chebyshev_minimax_lower
#check @chebyshev1.chebyshev_minimax_attained
#check @chebyshev1.Stepsize.finalExact_iff_permutation

/-! Article: Theorem 4.1 [thm:prefix-kernel]. Kernel and gain of the semi-iterative method. -/
#check @chebyshev1.Prefix.kernel_zero
#check @chebyshev1.Prefix.kernel_succ
#check @chebyshev1.Prefix.gain_exact
#check @chebyshev1.Prefix.gain_exact_sum
#check @chebyshev1.Prefix.gain_isEquivalent_rpow
#check @chebyshev1.Prefix.tail_column
#check @chebyshev1.Prefix.tail_fundamental
#check @chebyshev1.Prefix.beta_optimal_limit
#check @chebyshev1.Prefix.gamma_optimal_limit
#check @chebyshev1.Background.prefix_first_weights
#check @chebyshev1.Background.heavyBall_optimal_parameters
#check @chebyshev1.Background.heavyBall_rate_isLeast
#check @chebyshev1.Background.heavyBall_rate_eq_iff

/-! Article: Theorem 5.1 [thm:jacobi-method]. Jacobi method. -/
#check @chebyshev1.JacobiData.fixed_point
#check @chebyshev1.JacobiData.quadraticError_exact
#check @chebyshev1.JacobiData.terminal_exact
#check @chebyshev1.JacobiData.admissible_of_spectrum
#check @chebyshev1.JacobiData.residualPolynomial_eq
#check @chebyshev1.JacobiData.terminal_residual
#check @chebyshev1.JacobiData.terminal_residual_iff_monic
#check @chebyshev1.JacobiData.terminal_monic_iff_spectrum
#check @chebyshev1.JacobiData.terminal_scalar_iff_spectrum
#check @chebyshev1.TwoTerm.PositiveFixedPointUpTo
#check @chebyshev1.TwoTerm.exists_finite_jacobi_coordinates
#check @chebyshev1.TwoTerm.exists_terminal_jacobi_coordinates
#check @chebyshev1.Background.finite_favard_exists
#check @chebyshev1.Background.finite_favard_unique
#check @chebyshev1.Background.finite_jacobi_simple
#check @chebyshev1.Background.finite_jacobi_first_weights_pos
#check @chebyshev1.Background.terminal_recordedCG

/-! Article: Theorem 5.2 [thm:jacobi-first-variation-kernel]. Jacobi first-variation kernel. -/
#check @chebyshev1.JacobiData.block_eq_charpoly
#check @chebyshev1.JacobiData.matrix_principal_block
#check @chebyshev1.JacobiData.kernel_eq
#check @chebyshev1.JacobiData.kernelNorm_eq_blocks
#check @chebyshev1.JacobiData.gain_eq_blocks

/-! Article: Lemma 5.1 [lem:green-mass]. Green mass. -/
#check @chebyshev1.JacobiData.endpointProfile
#check @chebyshev1.JacobiData.endpointProfile_eq_resolvent
#check @chebyshev1.JacobiData.endpointProfile_mass
#check @chebyshev1.TwoTerm.finite_terminal_green_profile
#check @chebyshev1.Realization.signedEndpointProfile
#check @chebyshev1.Realization.signedEndpointProfile_mass
#check @chebyshev1.JacobiData.signedEndpointProfile_eq

/-! Article: Proposition 5.1 [prop:universal-lower]. Universal lower bound. -/
#check @chebyshev1.JacobiData.endpointEnergy_gap
#check @chebyshev1.JacobiData.spectrum_subset_of_terminal
#check @chebyshev1.JacobiData.admissible_of_terminal
#check @chebyshev1.JacobiData.gain_lower_bound_of_terminal
#check @chebyshev1.TwoTerm.finite_terminal_gain_lower
#check @chebyshev1.Realization.signedEndpointEnergy_gap
#check @chebyshev1.Realization.signedEndpointEnergy_ge_cube
#check @chebyshev1.Realization.signedEndpointEnergy_eq_cube_iff
#check @chebyshev1.Realization.kernelNorm_eq_signedEndpointEnergy
#check @chebyshev1.Realization.finalExact_gain_lower_bound
#check @chebyshev1.Realization.finalExact_gain_eq_lower_imp_flat

/-! Article: Remark 5.1 [rem:schur]. Momentum spreads the Green mass. -/
#check @chebyshev1.JacobiData.endpointEnergy_upper_bound
#check @chebyshev1.Stepsize.endpoint_square_sum
#check @chebyshev1.SpectralBasis.weight_doublyStochastic
#check @chebyshev1.SpectralBasis.diagonal_convex_permutations
#check @chebyshev1.SpectralBasis.diagonal_convex_sum_le
#check @chebyshev1.SpectralBasis.resolvent_convex_sum_le
#check @chebyshev1.Stepsize.signedEndpointProfile_eq_permutation

/-! Article: Lemma 6.1 [lem:reversal]. Time reversal. -/
#check @chebyshev1.JacobiData.endpointProfile_reversed
#check @chebyshev1.JacobiData.endpointEnergy_reversed
#check @chebyshev1.JacobiData.kernel_reversed
#check @chebyshev1.JacobiData.gain_reversed_of_terminal
#check @chebyshev1.JacobiData.spectral_weight_reversed
#check @chebyshev1.JacobiData.spectral_endpoint_weight_normalized
#check @chebyshev1.SineJacobi.spectral_weight_reversal
#check @chebyshev1.SineJacobi.sine_weights_reversal_fixed_iff
#check @chebyshev1.SineJacobi.sine_logWeights_stationary
#check @chebyshev1.TwoTerm.isotropicGossipGamma_spectral
#check @chebyshev1.JacobiData.isotropicGossipGamma_reversed
#check @chebyshev1.TwoTerm.frameGossipGamma_eq_impulse_hsSq
#check @chebyshev1.JacobiData.meanZeroGossipGamma_reversed
#check @chebyshev1.SpectralBasis.frameError_norm
#check @chebyshev1.SpectralBasis.frame_dimension
#check @chebyshev1.SpectralBasis.frameSphere_range_meanZero
#check @chebyshev1.Background.exists_weightedGraph_spectral_frame
#check @chebyshev1.JacobiData.connectedGraph_meanZero_reversal

/-! Article: Theorem 6.1 [thm:sine-lattice-main]. The sine--Jacobi matrix. -/
#check @chebyshev1.SineJacobi.method_initial
#check @chebyshev1.SineJacobi.method_coefficients
#check @chebyshev1.SineJacobi.quadraticError_exact
#check @chebyshev1.SineJacobi.leading_endpoint_max
#check @chebyshev1.SineJacobi.kernel_abs_le_endpoint
#check @chebyshev1.SineJacobi.gain_eq_endpoint
#check @chebyshev1.SineJacobi.couplingSq_pos
#check @chebyshev1.SineJacobi.terminal
#check @chebyshev1.SineJacobi.spectrum_eq_nodes
#check @chebyshev1.SineJacobi.matrix_persymmetric
#check @chebyshev1.SineJacobi.spectral_weight
#check @chebyshev1.SineJacobi.coupling_expansion_uniform
#check @chebyshev1.SineJacobi.coupling_fourth_order_error_le
#check @chebyshev1.SineJacobi.scaledCorrection_mesh_uniform
#check @chebyshev1.SineJacobi.rogers_recurrence
#check @chebyshev1.SineJacobi.rogers_terminal
#check @chebyshev1.SineJacobi.normalized_fourier
#check @chebyshev1.SineJacobi.normalizedCoefficient_sum
#check @chebyshev1.SineJacobi.leading_orthogonality
#check @chebyshev1.SineJacobi.leading_norm_positive
#check @chebyshev1.JacobiData.block_eval_pos_of_spectrum
#check @chebyshev1.JacobiData.admissible_of_spectrum
#check @chebyshev1.SineJacobi.admissible
#check @chebyshev1.Continuant.interior_identity
#check @chebyshev1.SineJacobi.blockFourier_interior_nonneg
#check @chebyshev1.SineJacobi.endpointMax

/-! Article: Theorem 6.2 [thm:sine-endpoint-profile]. Sine--Jacobi profile and gain. -/
#check @chebyshev1.SineJacobi.sineIntegral_eq
#check @chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit
#check @chebyshev1.SineJacobi.greenWeight_energy_limit
#check @chebyshev1.SineJacobi.endpoint_second_difference
#check @chebyshev1.SineJacobi.endpoint_global_bound
#check @chebyshev1.SineJacobi.sineProfile_pos
#check @chebyshev1.SineJacobi.sineProfile_boundary
#check @chebyshev1.SineJacobi.sineProfile_ode
#check @chebyshev1.SineJacobi.sineProfile_unique
#check @chebyshev1.SineJacobi.ratio_scaled_limit
#check @chebyshev1.SineJacobi.convolutionIntegral_limit
#check @chebyshev1.SineJacobi.convolutionIntegral_eq_elliptic
#check @chebyshev1.SineJacobi.endpointProfile_uniformOn
#check @chebyshev1.SineJacobi.greenProfile_eLpNorm_limit
#check @chebyshev1.SineJacobi.endpoint_product_sum_limit
#check @chebyshev1.SineJacobi.endpoint_product_square_sum_limit
#check @chebyshev1.SineJacobi.gain_exact
#check @chebyshev1.SineJacobi.gain_exact_resolvent
#check @chebyshev1.SineJacobi.resolvent_trace
#check @chebyshev1.SineJacobi.gain_isEquivalent
#check @chebyshev1.SineJacobi.gain_eventually_lt_prefix
#check @chebyshev1.SineJacobi.sineEnergy
#check @chebyshev1.SineJacobi.sineEnergy_ge_one
#check @chebyshev1.SineJacobi.sineEnergy_le_four_div_pi
#check @chebyshev1.SineJacobi.sineEnergy_lt_four_thirds
#check @chebyshev1.SineJacobi.gainConstant_rounding
#check @chebyshev1.SineJacobi.relativeGainImprovement_rounding
#check @chebyshev1.SineJacobi.squaredGainImprovement_rounding
#check @chebyshev1.SineJacobi.universalLowerGap_rounding
#check @chebyshev1.SineJacobi.prefixGainConstant_rounding

/-! Article: Theorem 7.1 [thm:finite-drift]. Finite Hessian drift in Jacobi coordinates. -/
#check @chebyshev1.JacobiData.insertionTerm_blocks
#check @chebyshev1.JacobiData.driftOrder_normalized
#check @chebyshev1.JacobiData.operatorTransfer_driftOrders
#check @chebyshev1.JacobiData.G_eq_normalized_partitionBound
#check @chebyshev1.JacobiData.opNorm_driftOrder_G_le
#check @chebyshev1.JacobiData.G_ge_chebyshev_coeff_all
#check @chebyshev1.JacobiData.G_eq_chebyshev_coeff_all
#check @chebyshev1.JacobiData.opNorm_finiteDrift_endpoint_le
#check @chebyshev1.JacobiData.opNorm_driftRemainder_endpoint_le
#check @chebyshev1.JacobiData.opNorm_driftRemainder_cosh_le
#check @chebyshev1.Realization.static_shift_lower_bounds_general
#check @chebyshev1.Realization.static_shift_attained
#check @chebyshev1.JacobiData.opNorm_driftOrder_static
#check @chebyshev1.SpectralInterval.expanded_residual_isGreatest

/-! Article: Corollary 7.1 [cor:prefix-finite-drift]. Finite drift for the two momentum methods. -/
#check @chebyshev1.Prefix.opNorm_linearResponse_le
#check @chebyshev1.Prefix.opNorm_finiteDrift_le
#check @chebyshev1.Prefix.opNorm_driftRemainder_le
#check @chebyshev1.Prefix.opNorm_driftRemainder_cosh_le
#check @chebyshev1.Prefix.static_shift_attained
#check @chebyshev1.SineJacobi.G_exact
#check @chebyshev1.SineJacobi.opNorm_linearResponse_le
#check @chebyshev1.SineJacobi.opNorm_finiteDrift_le
#check @chebyshev1.SineJacobi.opNorm_driftRemainder_le
#check @chebyshev1.SineJacobi.opNorm_driftRemainder_cosh_le
#check @chebyshev1.SineJacobi.static_shift_attained
#check @chebyshev1.SineJacobi.driftOrder_static_attained
#check @chebyshev1.Prefix.jacobiBlock_leading
#check @chebyshev1.Prefix.jacobiBlock_interior

/-! Article: Theorem 7.2 [thm:local-rate]. Local linear convergence. -/
#check @chebyshev1.Nonlinear.HessianControl
#check @chebyshev1.Nonlinear.lipschitzHessian_confinement
#check @chebyshev1.Nonlinear.lipschitzHessian_local_error_le
#check @chebyshev1.Nonlinear.lipschitzHessian_local_accelerated_le
#check @chebyshev1.Nonlinear.restartHorizon
#check @chebyshev1.Nonlinear.lipschitzHessian_halving
#check @chebyshev1.Nonlinear.restartedError_horizon_le
#check @chebyshev1.Nonlinear.restartCount
#check @chebyshev1.Nonlinear.restartedError_target_le
#check @chebyshev1.Nonlinear.hessianControl_translate
#check @chebyshev1.Nonlinear.lipschitzHessian_confinement_at
#check @chebyshev1.Nonlinear.lipschitzHessian_local_error_le_at

/-! Article: Theorem 7.3 [thm:second-order]. Second-order error along the trajectory. -/
#check @chebyshev1.Nonlinear.leadingRadius
#check @chebyshev1.Nonlinear.secondOrderCoefficient
#check @chebyshev1.Nonlinear.secondOrderCoefficient_nonneg
#check @chebyshev1.Nonlinear.secondOrderCoefficient_le_sq
#check @chebyshev1.Nonlinear.nonlinear_error_duhamel
#check @chebyshev1.Nonlinear.lipschitzHessian_weighted_discrepancy_le
#check @chebyshev1.Nonlinear.cubicErrorPolynomial_eval
#check @chebyshev1.Nonlinear.cubicErrorPolynomial_coeff_two
#check @chebyshev1.Nonlinear.cubic_weighted_sharpness
#check @chebyshev1.Nonlinear.cubic_weighted_norm_sharpness
#check @chebyshev1.Nonlinear.polynomial_third_order_factor
#check @chebyshev1.Nonlinear.cubic_weighted_remainder_isBigO
#check @chebyshev1.Nonlinear.leadingRadius_isGreatest
#check @chebyshev1.Nonlinear.lipschitzHessian_weighted_discrepancy_le_at

/-! Article: Remark 7.1 [rem:CN]. Size of C_N. -/
#check @chebyshev1.Nonlinear.prefix_secondOrderCoefficient_sum
#check @chebyshev1.Nonlinear.prefixSecondOrderRiemann_error
#check @chebyshev1.Nonlinear.prefixSecondOrderProfile_integral
#check @chebyshev1.Nonlinear.prefix_secondOrderCoefficient_integral_limit
#check @chebyshev1.Nonlinear.prefixSecondOrderProfile_infinite
#check @chebyshev1.Nonlinear.prefixSecondOrderProfile_strictMonoOn
#check @chebyshev1.Nonlinear.prefixSecondOrderProfile_monotoneOn
#check @chebyshev1.Nonlinear.prefixSecondOrderProfile_lt_pi_div_two

/-! Article: Lemma 8.1 [lem:perturbed-run]. Perturbed runs. -/
#check @chebyshev1.Perturbations.forcedOrbit_eq
#check @chebyshev1.TwoTerm.forcingTail
#check @chebyshev1.TwoTerm.perturbedError_eq_residual_add_forcing
#check @chebyshev1.TwoTerm.nonlinearError_eq_quadratic_add_forcing

/-! Article: Proposition 8.1 [prop:random-runs]. Random perturbations. -/
#check @chebyshev1.Stochastic.martingaleDifference_sum_norm_sq
#check @chebyshev1.TwoTerm.stochasticError
#check @chebyshev1.TwoTerm.stochasticError_expansion
#check @chebyshev1.TwoTerm.stochasticError_mean_variance
#check @chebyshev1.Stochastic.quadratic_mean_decomposition
#check @chebyshev1.TwoTerm.quadraticNoiseGamma
#check @chebyshev1.TwoTerm.quadraticNoiseRemainder
#check @chebyshev1.TwoTerm.quadraticNoiseRemainder_nonneg
#check @chebyshev1.TwoTerm.stochasticError_quadratic_covariance
#check @chebyshev1.TwoTerm.QuadraticOracle
#check @chebyshev1.TwoTerm.covarianceRemainderBound
#check @chebyshev1.TwoTerm.QuadraticOracle.secondMoment_bound
#check @chebyshev1.TwoTerm.QuadraticOracle.remainder_bound
#check @chebyshev1.TwoTerm.quadraticNoiseRemainder_isBigO
#check @chebyshev1.TwoTerm.quadraticNoiseRemainder_dropout_isBigO
#check @chebyshev1.TwoTerm.MatrixQuadraticOracle
#check @chebyshev1.TwoTerm.MatrixQuadraticOracle.toObservationOracle
#check @chebyshev1.TwoTerm.MatrixQuadraticOracle.variance_expansion
#check @chebyshev1.TwoTerm.MatrixQuadraticOracle.remainder_nonneg
#check @chebyshev1.TwoTerm.MatrixQuadraticOracle.remainder_bound
#check @chebyshev1.TwoTerm.matrixNoiseRemainder_isBigO_of_eventually

/-! Article: Remark 8.1 [rem:stochastic]. Stochastic curvature. -/
#check @chebyshev1.Realization.linearResponse_coordinates
#check @chebyshev1.Realization.hsNorm_linearResponse_bound
#check @chebyshev1.TwoTerm.quadraticNoiseGamma
#check @chebyshev1.Stochastic.uniformSphere_hsNorm_identity
#check @chebyshev1.Stochastic.independent_matrix_isotropic_spectral
#check @chebyshev1.Stochastic.independent_matrix_isotropic_iid_bound
#check @chebyshev1.Stochastic.independent_matrix_isotropic_iid_attained
#check @chebyshev1.TwoTerm.matrixCurvatureError
#check @chebyshev1.TwoTerm.matrixCurvatureError_regular
#check @chebyshev1.TwoTerm.independentMatrixOracle
#check @chebyshev1.TwoTerm.matrixCurvatureGamma_sphere_spectral
#check @chebyshev1.TwoTerm.sphereCurvature_variance_expansion
#check @chebyshev1.TwoTerm.sphereCurvatureRemainder_nonneg
#check @chebyshev1.TwoTerm.sphereCurvatureRemainder_bound
#check @chebyshev1.TwoTerm.sphereCurvatureRemainder_isBigO
#check @chebyshev1.TwoTerm.sphereCurvature_of_iIndepFun
#check @chebyshev1.Stochastic.matrix_entry_memLp_iff_hsSq_integrable
#check @chebyshev1.Stochastic.finite_independent_matrix_isotropic_spectral
#check @chebyshev1.Stochastic.finite_independent_matrix_isotropic_iid_bound
#check @chebyshev1.Stochastic.finite_iid_spectralEnergy_attained
#check @chebyshev1.Stochastic.finite_iid_eigenspace_energy_attained
#check @chebyshev1.Stochastic.finite_independent_matrix_iid_eigenspace_attained
#check @chebyshev1.TwoTerm.finiteSphereCurvature_of_iIndepFun

/-! Article: Proposition 8.2 [prop:first-step]. First-step transmission. -/
#check @chebyshev1.Prefix.first_step_transmission
#check @chebyshev1.JacobiData.kernel_zero_input_independent
#check @chebyshev1.JacobiData.first_step_transmission_of_terminal
#check @chebyshev1.SineJacobi.first_green_spectral_sum
#check @chebyshev1.SineJacobi.first_green_cotangent_sum
#check @chebyshev1.SineJacobi.first_green_error_bound
#check @chebyshev1.SineJacobi.first_green_error_isBigO
#check @chebyshev1.JacobiData.endpointProfile_reversed

/-! Article: Corollary 8.1 [cor:models]. Leading terms. -/
#check @chebyshev1.TwoTerm.nonlinearError_second_order
#check @chebyshev1.TwoTerm.quadraticCorrection_eq_sum
#check @chebyshev1.TwoTerm.quadraticError_neg
#check @chebyshev1.TwoTerm.quadraticCorrection_neg
#check @chebyshev1.TwoTerm.objectiveError_second_order
#check @chebyshev1.TwoTerm.objectiveError_radialNorm
#check @chebyshev1.Perturbations.radialSlope
#check @chebyshev1.Perturbations.radialNorm_hasDerivWithinAt
#check @chebyshev1.Perturbations.gradient_second_derivative_inner
#check @chebyshev1.Perturbations.coordinate_gradient_second_derivative_inner
#check @chebyshev1.TwoTerm.gossipError
#check @chebyshev1.TwoTerm.gossipError_eq_stochasticError
#check @chebyshev1.TwoTerm.gossipError_regular
#check @chebyshev1.TwoTerm.gossipQuadraticOracle
#check @chebyshev1.TwoTerm.gossipGamma_residual
#check @chebyshev1.TwoTerm.gossipError_variance_expansion
#check @chebyshev1.TwoTerm.gossipError_secondMoment_expansion
#check @chebyshev1.TwoTerm.gossipRemainder_nonneg
#check @chebyshev1.TwoTerm.gossipRemainder_bound
#check @chebyshev1.TwoTerm.gossipRemainder_isBigO
#check @chebyshev1.Stochastic.dropoutNoise
#check @chebyshev1.Stochastic.dropoutNoise_mean
#check @chebyshev1.Stochastic.dropoutNoise_variance
#check @chebyshev1.Stochastic.dropout_sum_secondMoment
#check @chebyshev1.Stochastic.incidence
#check @chebyshev1.Stochastic.edgeLaplacian
#check @chebyshev1.Stochastic.gossipOracleNoise_eq
#check @chebyshev1.Stochastic.gossipOracleNoise_secondMoment
#check @chebyshev1.TwoTerm.variableError_sum_invariant
#check @chebyshev1.Perturbations.ThreeTimesDifferentiableAtZero
#check @chebyshev1.TwoTerm.objectiveError_vector_second_order
#check @chebyshev1.Perturbations.coordinate_gradientLinearization
#check @chebyshev1.Perturbations.coordinate_gradient_second_derivative
#check @chebyshev1.Nonlinear.objectiveError_full_expansion
#check @chebyshev1.Nonlinear.objectiveSecondVariation_norm_le
#check @chebyshev1.Nonlinear.objectiveSecondVariation_norm_le_of_lipschitz_near
#check @chebyshev1.Background.weightedLaplacian_kernel_iff
#check @chebyshev1.Background.weightedLaplacian_meanZero_pos
#check @chebyshev1.Background.weightedLaplacian_spectral_gap
#check @chebyshev1.TwoTerm.gossipError_regular_finite
#check @chebyshev1.TwoTerm.gossipQuadraticOracle_finite
#check @chebyshev1.TwoTerm.gossipError_mean_finite
#check @chebyshev1.TwoTerm.gossipError_variance_finite
#check @chebyshev1.TwoTerm.gossipError_secondMoment_finite
#check @chebyshev1.TwoTerm.gossipCovarianceRemainder_nonneg
#check @chebyshev1.TwoTerm.gossipCovarianceRemainder_bound_finite
#check @chebyshev1.TwoTerm.FiniteGossipSamples
#check @chebyshev1.TwoTerm.gossipCovarianceRemainder_isBigO_varyingMeasure_finite
#check @chebyshev1.JacobiData.method_scale
#check @chebyshev1.JacobiData.unscaledGossipError_scale
#check @chebyshev1.JacobiData.unscaledGossipDiscrepancy_scale
#check @chebyshev1.Perturbations.gradient_translate
#check @chebyshev1.Perturbations.gradient_derivative_translate
#check @chebyshev1.Perturbations.gradient_second_derivative_translate
#check @chebyshev1.Perturbations.threeTimesDifferentiableAtZero_translate
#check @chebyshev1.Nonlinear.objectiveError_full_expansion_at

/-! Article: Lemma A.1 [lem:pit]. Prefix--insertion--tail factorization. -/
#check @chebyshev1.TwoTerm.kernel_factor
#check @chebyshev1.TwoTerm.forcingTail
#check @chebyshev1.TwoTerm.forcingTail_eq_memoryProduct

/-! Article: Lemma D.1 [lem:root-unity-rogers]. Explicit leading polynomials. -/
#check @chebyshev1.SineJacobi.rogers_recurrence
#check @chebyshev1.SineJacobi.rogers_terminal
#check @chebyshev1.SineJacobi.normalized_fourier
#check @chebyshev1.SineJacobi.normalizedCoefficient_sum
#check @chebyshev1.SineJacobi.leading_norm_positive

/-! Article: Theorem D.1 [thm:discrete-hard-edge-LG]. Endpoint asymptotics of the sine hard-edge recurrence. -/
#check @chebyshev1.SineJacobi.endpoint_second_difference
#check @chebyshev1.SineJacobi.endpoint_global_bound
#check @chebyshev1.SineJacobi.sineProfile_pos
#check @chebyshev1.SineJacobi.sineProfile_boundary
#check @chebyshev1.SineJacobi.sineProfile_ode
#check @chebyshev1.SineJacobi.sineProfile_unique
#check @chebyshev1.SineJacobi.ratio_scaled_limit
#check @chebyshev1.SineJacobi.convolutionIntegral_limit
#check @chebyshev1.SineJacobi.convolutionIntegral_eq_elliptic
#check @chebyshev1.SineJacobi.endpointProfile_uniformOn
#check @chebyshev1.SineJacobi.greenProfile_eLpNorm_limit

/-! Article: Lemma D.2 [lem:sine-block-positivity]. Fourier positivity of the sine blocks. -/
#check @chebyshev1.Continuant.interior_identity
#check @chebyshev1.SineJacobi.blockFourier_interior_nonneg
#check @chebyshev1.SineJacobi.endpointMax

/-! Article: Lemma S1.1 [lem:persymmetry]. Persymmetric Jacobi matrices. -/
#check @chebyshev1.JacobiData.spectral_weight_cofactor
#check @chebyshev1.JacobiData.spectral_endpoint_product
#check @chebyshev1.JacobiData.block_pair_unique
#check @chebyshev1.JacobiData.persymmetric_iff_spectral_weights
#check @chebyshev1.JacobiData.persymmetric_iff_normalized_spectral_weights
#check @chebyshev1.Background.signed_endpoint_residue
#check @chebyshev1.Background.endpoint_adjugate

/-! Article: Corollary S2.1 [cor:finite-comparison]. Finite-horizon gain comparison. -/
#check @chebyshev1.Stepsize.lowerBound_square_sub_prefix_gain_square
#check @chebyshev1.Stepsize.gain_square_sub_prefix_gain_square
#check @chebyshev1.Stepsize.prefix_gap_pos
#check @chebyshev1.Stepsize.prefix_gain_lt
#check @chebyshev1.Stepsize.lowerBound_div_prefix_isEquivalent

/-! Article: Proposition S4.1 [prop:variance-polynomial]. Variance polynomial. -/
#check @chebyshev1.Realization.scalarNoise_expansion
#check @chebyshev1.Realization.scalarNoiseOutput_expansion
#check @chebyshev1.Realization.scalarNoise_mean
#check @chebyshev1.Realization.scalarNoiseEnergy_nonneg
#check @chebyshev1.Realization.scalarNoise_variance
#check @chebyshev1.Realization.scalarNoise_variance_leading
#check @chebyshev1.Realization.scalarNoiseRemainder_nonneg
#check @chebyshev1.Realization.scalarNoiseRemainder_isBigO
#check @chebyshev1.Realization.scalarNoiseCoefficient_singleton
#check @chebyshev1.Realization.scalarNoiseEnergy_one
#check @chebyshev1.Realization.finiteScalarNoise_mean
#check @chebyshev1.Realization.finiteScalarNoise_secondMoment
#check @chebyshev1.Realization.finiteScalarNoise_variance
#check @chebyshev1.Realization.finiteScalarNoise_variance_leading

/-! Article: Proposition S4.2 [prop:radial-derivative]. Radial derivative. -/
#check @chebyshev1.TwoTerm.nonlinearError_second_order
#check @chebyshev1.TwoTerm.quadraticCorrection_eq_sum
#check @chebyshev1.TwoTerm.quadraticError_neg
#check @chebyshev1.TwoTerm.quadraticCorrection_neg
#check @chebyshev1.TwoTerm.objectiveError_second_order
#check @chebyshev1.TwoTerm.objectiveError_radialNorm
#check @chebyshev1.Perturbations.radialSlope
#check @chebyshev1.Perturbations.radialNorm_hasDerivWithinAt
#check @chebyshev1.Perturbations.gradient_second_derivative_inner
#check @chebyshev1.Perturbations.coordinate_gradient_second_derivative_inner

/-! Article: Algorithm S1 [alg:prefix]. Chebyshev semi-iterative method. -/
#check @chebyshev1.JacobiData.ratioState
#check @chebyshev1.JacobiData.ratioState_eq_den_ratio
#check @chebyshev1.JacobiData.ratioDenominator_pos
#check @chebyshev1.JacobiData.ratioMethod_quadraticError
#check @chebyshev1.Prefix.ratioMethod_eq
#check @chebyshev1.Prefix.ratio_quadraticError_exact

/-! Article: Algorithm S2 [alg:sine]. Sine--Jacobi method. -/
#check @chebyshev1.SineJacobi.ratio_initial
#check @chebyshev1.SineJacobi.ratio_coefficients
#check @chebyshev1.SineJacobi.ratio_quadraticError_exact
#check @chebyshev1.JacobiData.ratioMethod_nonlinearError
#check @chebyshev1.SineJacobi.ratio_nonlinearError
