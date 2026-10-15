import «2606.16671v2»

/-!
Article: 2606.16671v2 — statements in the order of the article.
Use: imported by `Check`; all references below are type-checked, and their proof bodies
are included in its module-owned axiom audit. Comments explain numerical exclusions.
The showcase introduces no additional mathematical hypotheses.
-/

/-!
2606.16671v2, Lemma 1.1. First-order expansion of the transfer.
-/
#check @«2606.16671v2».Realization.hasDerivAt_operatorTransfer
#check @«2606.16671v2».Realization.linearResponse_eq_sum
#check @«2606.16671v2».Realization.spectralPair_linearResponse
#check @«2606.16671v2».Realization.linearResponse_coordinates

/-!
2606.16671v2, Definition 1.2. Realizations, kernels and Hessian-drift gain.
-/
#check @«2606.16671v2».Realization
#check @«2606.16671v2».Realization.scalarStep
#check @«2606.16671v2».Realization.operatorTransfer
#check @«2606.16671v2».Realization.residualPolynomial
#check @«2606.16671v2».Realization.kernel
#check @«2606.16671v2».Realization.kernelNorm
#check @«2606.16671v2».Realization.gain

/-!
2606.16671v2, Proposition 1.3. Finite expansion, Hilbert–Schmidt bound and sharpness.
-/
#check @«2606.16671v2».orderedProduct_add_expansion
#check @«2606.16671v2».insertionMultilinear
#check @«2606.16671v2».Realization.finiteDrift_polynomial_decomposition
#check @«2606.16671v2».Realization.operatorTransfer_affine_by_degree
#check @«2606.16671v2».Realization.hsNorm_linearResponse_bound
#check @«2606.16671v2».Realization.hs_bound_attained
#check @«2606.16671v2».Realization.hs_constant_minimal
#check @«2606.16671v2».Realization.gain_attained

/-!
2606.16671v2, Theorem 1.4. Sharp stepsize drift lower bound and asymptotics.
-/
#check @«2606.16671v2».Stepsize.endpoint_square_sum
#check @«2606.16671v2».Stepsize.gain_lower_bound
#check @«2606.16671v2».Stepsize.correction_error_isBigO
#check @«2606.16671v2».Stepsize.lowerBound_asymptotic

/-!
2606.16671v2, Theorem 2.1. Prefix-exact recurrence and quadratic transfer.
-/
#check @«2606.16671v2».Prefix.residualPolynomial_eq
#check @«2606.16671v2».Prefix.operator_exact
#check @«2606.16671v2».Prefix.quadraticError_exact
#check @«2606.16671v2».Prefix.quadraticError_eq_transfer

/-!
2606.16671v2, Theorem 2.2. Exact prefix kernel, gain and asymptotics.
-/
#check @«2606.16671v2».Prefix.kernel_zero
#check @«2606.16671v2».Prefix.kernel_succ
#check @«2606.16671v2».Prefix.gain_exact
#check @«2606.16671v2».Prefix.gain_exact_sum
#check @«2606.16671v2».Prefix.gain_isEquivalent_rpow

/-!
2606.16671v2, Theorem 3.1. Optimality among causal two-term prefix methods.
-/
#check @«2606.16671v2».TwoTerm.kernel_eq_prefix
#check @«2606.16671v2».TwoTerm.gain_eq_prefix
#check @«2606.16671v2».TwoTerm.optimal_gain
#check @«2606.16671v2».TwoTerm.standard_attains
#check @«2606.16671v2».TwoTerm.optimal_asymptotic

/-!
2606.16671v2, Theorem 4.1. Jacobi recurrence, fixed point and terminal exactness.
-/
#check @«2606.16671v2».JacobiData.fixed_point
#check @«2606.16671v2».JacobiData.quadraticError_exact
#check @«2606.16671v2».JacobiData.terminal_exact

/-!
2606.16671v2, Theorem 4.2. Block determinants, first-variation kernel and gain.
-/
#check @«2606.16671v2».JacobiData.block_eq_charpoly
#check @«2606.16671v2».JacobiData.matrix_principal_block
#check @«2606.16671v2».JacobiData.kernel_eq
#check @«2606.16671v2».JacobiData.kernelNorm_eq_blocks
#check @«2606.16671v2».JacobiData.gain_eq_blocks

/-!
2606.16671v2, Theorem 4.3. All insertion orders, partition bounds, finite/cosh bounds and
attainment.
-/
#check @«2606.16671v2».JacobiData.insertionTerm_blocks
#check @«2606.16671v2».JacobiData.driftOrder_normalized
#check @«2606.16671v2».JacobiData.operatorTransfer_driftOrders
#check @«2606.16671v2».JacobiData.G_eq_normalized_partitionBound
#check @«2606.16671v2».JacobiData.opNorm_driftOrder_G_le
#check @«2606.16671v2».JacobiData.G_ge_chebyshev_coeff_all
#check @«2606.16671v2».JacobiData.G_eq_chebyshev_coeff_all
#check @«2606.16671v2».JacobiData.opNorm_finiteDrift_endpoint_le
#check @«2606.16671v2».JacobiData.opNorm_driftRemainder_endpoint_le
#check @«2606.16671v2».JacobiData.opNorm_driftRemainder_cosh_le
#check @«2606.16671v2».Realization.static_shift_lower_bounds_general
#check @«2606.16671v2».Realization.static_shift_attained
#check @«2606.16671v2».JacobiData.opNorm_driftOrder_static

/-!
2606.16671v2, Corollary 4.4. Attained finite-drift bounds for the prefix recurrence.
-/
#check @«2606.16671v2».Prefix.opNorm_linearResponse_le
#check @«2606.16671v2».Prefix.opNorm_finiteDrift_le
#check @«2606.16671v2».Prefix.opNorm_driftRemainder_le
#check @«2606.16671v2».Prefix.opNorm_driftRemainder_cosh_le
#check @«2606.16671v2».Prefix.static_shift_attained

/-!
2606.16671v2, Algorithm 1. Explicit prefix-exact gradient recurrence.
-/
#check @«2606.16671v2».Prefix.algorithmStep_succ
#check @«2606.16671v2».Prefix.beta_coefficient
#check @«2606.16671v2».Prefix.realization
#check @«2606.16671v2».Prefix.scalarStep_zero

/-!
2606.16671v2, Algorithm 2. Explicit sine–Jacobi gradient recurrence.
-/
#check @«2606.16671v2».SineJacobi.method_initial
#check @«2606.16671v2».SineJacobi.method_coefficients
#check @«2606.16671v2».SineJacobi.quadraticError_exact

/-!
2606.16671v2, Theorem 5.1. Endpoint-profile L2 convergence and limiting Green energy.
-/
#check @«2606.16671v2».SineJacobi.sineIntegral_eq
#check @«2606.16671v2».SineJacobi.diagonalProfile_eLpNorm_limit
#check @«2606.16671v2».SineJacobi.greenWeight_energy_limit

/-!
2606.16671v2, Theorem 5.2. Exact sine gain, resolvent expression, asymptotics and energy value.
-/
#check @«2606.16671v2».SineJacobi.gain_exact
#check @«2606.16671v2».SineJacobi.gain_exact_resolvent
#check @«2606.16671v2».SineJacobi.resolvent_trace
#check @«2606.16671v2».SineJacobi.gain_isEquivalent
#check @«2606.16671v2».SineJacobi.gain_eventually_lt_prefix
#check @«2606.16671v2».SineJacobi.sineEnergy
#check @«2606.16671v2».SineJacobi.sineEnergy_ge_one
#check @«2606.16671v2».SineJacobi.sineEnergy_le_four_div_pi
#check @«2606.16671v2».SineJacobi.sineEnergy_lt_four_thirds
#check @«2606.16671v2».SineJacobi.sineEnergy_decimal
#check @«2606.16671v2».SineJacobi.sineEnergy_rounding

/-!
2606.16671v2, Corollary 5.3. Attained finite-drift bounds for the sine chain.
-/
#check @«2606.16671v2».SineJacobi.G_exact
#check @«2606.16671v2».SineJacobi.opNorm_linearResponse_le
#check @«2606.16671v2».SineJacobi.opNorm_finiteDrift_le
#check @«2606.16671v2».SineJacobi.opNorm_driftRemainder_le
#check @«2606.16671v2».SineJacobi.opNorm_driftRemainder_cosh_le
#check @«2606.16671v2».SineJacobi.static_shift_attained
#check @«2606.16671v2».SineJacobi.driftOrder_static_attained

/-!
2606.16671v2, Corollary 5.4. Lipschitz-Hessian error bound for both methods.
-/
#check @«2606.16671v2».Nonlinear.averagedDerivative_apply
#check @«2606.16671v2».Nonlinear.averagedDerivative_sub_norm_le
#check @«2606.16671v2».Nonlinear.lipschitzHessian_error_le

/-!
2606.16671v2, Remark 5.5. Exact drift scale, accuracy asymptotics and rational finite examples.
-/
#check @«2606.16671v2».SpectralInterval.amplification_cosh
#check @«2606.16671v2».SpectralInterval.amplification_effectiveKappa_le
#check @«2606.16671v2».SpectralInterval.drift_scale_limit
#check @«2606.16671v2».SpectralInterval.drift_factor_limit
#check @«2606.16671v2».SpectralInterval.logarithmic_drift_scale_limit
#check @«2606.16671v2».Realization.static_shift_at_mu
#check @«2606.16671v2».terminal_log_accuracy_ratio_limit
#check @«2606.16671v2».low_accuracy_amplification_ratio_limit
#check @«2606.16671v2».terminal_certificate
#check @«2606.16671v2».amplification_certificate_one_percent
#check @«2606.16671v2».amplification_certificate_five_percent
#check @«2606.16671v2».amplification_certificate_quarter

/-!
2606.16671v2, Section 6. Performance experiments. Omitted: Experimental runs and measured
performance are outside the mathematical proof scope.
-/

/-!
2606.16671v2, Appendix A. Proofs of Lemma 1.1, Proposition 1.3 and Theorem 1.4.
-/
#check @«2606.16671v2».Realization.hasDerivAt_operatorTransfer
#check @«2606.16671v2».Realization.linearResponse_eq_sum
#check @«2606.16671v2».Realization.spectralPair_linearResponse
#check @«2606.16671v2».Realization.linearResponse_coordinates
#check @«2606.16671v2».orderedProduct_add_expansion
#check @«2606.16671v2».insertionMultilinear
#check @«2606.16671v2».Realization.finiteDrift_polynomial_decomposition
#check @«2606.16671v2».Realization.operatorTransfer_affine_by_degree
#check @«2606.16671v2».Realization.hsNorm_linearResponse_bound
#check @«2606.16671v2».Realization.hs_bound_attained
#check @«2606.16671v2».Realization.hs_constant_minimal
#check @«2606.16671v2».Realization.gain_attained
#check @«2606.16671v2».Stepsize.endpoint_square_sum
#check @«2606.16671v2».Stepsize.gain_lower_bound
#check @«2606.16671v2».Stepsize.correction_error_isBigO
#check @«2606.16671v2».Stepsize.lowerBound_asymptotic

/-!
2606.16671v2, Lemma B.1. Chebyshev tail fundamental solution.
-/
#check @«2606.16671v2».Prefix.tail_column
#check @«2606.16671v2».Prefix.tail_fundamental

/-!
2606.16671v2, Theorem C.1. Local uniqueness of the causal two-term realization.
-/
#check @«2606.16671v2».TwoTerm.local_unique
#check @«2606.16671v2».TwoTerm.coefficients_unique_explicit

/-!
2606.16671v2, Appendix D. Proofs of the Jacobi block and all-order drift identities.
-/
#check @«2606.16671v2».JacobiData.fixed_point
#check @«2606.16671v2».JacobiData.quadraticError_exact
#check @«2606.16671v2».JacobiData.terminal_exact
#check @«2606.16671v2».JacobiData.block_eq_charpoly
#check @«2606.16671v2».JacobiData.matrix_principal_block
#check @«2606.16671v2».JacobiData.kernel_eq
#check @«2606.16671v2».JacobiData.kernelNorm_eq_blocks
#check @«2606.16671v2».JacobiData.gain_eq_blocks
#check @«2606.16671v2».JacobiData.insertionTerm_blocks
#check @«2606.16671v2».JacobiData.driftOrder_normalized
#check @«2606.16671v2».JacobiData.operatorTransfer_driftOrders
#check @«2606.16671v2».JacobiData.G_eq_normalized_partitionBound
#check @«2606.16671v2».JacobiData.opNorm_driftOrder_G_le
#check @«2606.16671v2».JacobiData.G_ge_chebyshev_coeff_all
#check @«2606.16671v2».JacobiData.G_eq_chebyshev_coeff_all
#check @«2606.16671v2».JacobiData.opNorm_finiteDrift_endpoint_le
#check @«2606.16671v2».JacobiData.opNorm_driftRemainder_endpoint_le
#check @«2606.16671v2».JacobiData.opNorm_driftRemainder_cosh_le
#check @«2606.16671v2».Realization.static_shift_lower_bounds_general
#check @«2606.16671v2».Realization.static_shift_attained
#check @«2606.16671v2».JacobiData.opNorm_driftOrder_static

/-!
2606.16671v2, Theorem E.1. Sine-lattice couplings, spectrum, expansion and symmetry.
-/
#check @«2606.16671v2».SineJacobi.leading_endpoint_max
#check @«2606.16671v2».SineJacobi.kernel_abs_le_endpoint
#check @«2606.16671v2».SineJacobi.gain_eq_endpoint

#check @«2606.16671v2».SineJacobi.couplingSq_pos
#check @«2606.16671v2».SineJacobi.terminal
#check @«2606.16671v2».SineJacobi.spectrum_eq_nodes
#check @«2606.16671v2».SineJacobi.matrix_persymmetric
#check @«2606.16671v2».SineJacobi.spectral_weight
#check @«2606.16671v2».SineJacobi.coupling_expansion_uniform
#check @«2606.16671v2».SineJacobi.coupling_fourth_order_error_le
#check @«2606.16671v2».SineJacobi.scaledCorrection_mesh_uniform

/-!
2606.16671v2, Lemma E.2. Root-of-unity Rogers recurrence, Fourier coefficients and orthogonality.
-/
#check @«2606.16671v2».SineJacobi.rogers_recurrence
#check @«2606.16671v2».SineJacobi.rogers_terminal
#check @«2606.16671v2».SineJacobi.normalized_fourier
#check @«2606.16671v2».SineJacobi.normalizedCoefficient_sum
#check @«2606.16671v2».SineJacobi.leading_orthogonality
#check @«2606.16671v2».SineJacobi.leading_norm_positive

/-!
2606.16671v2, Theorem E.3. Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
#check @«2606.16671v2».SineJacobi.endpoint_second_difference
#check @«2606.16671v2».SineJacobi.endpoint_global_bound
#check @«2606.16671v2».SineJacobi.sineProfile_pos
#check @«2606.16671v2».SineJacobi.sineProfile_boundary
#check @«2606.16671v2».SineJacobi.sineProfile_ode
#check @«2606.16671v2».SineJacobi.sineProfile_unique
#check @«2606.16671v2».SineJacobi.ratio_scaled_limit
#check @«2606.16671v2».SineJacobi.convolutionIntegral_limit
#check @«2606.16671v2».SineJacobi.convolutionIntegral_eq_elliptic
#check @«2606.16671v2».SineJacobi.endpointProfile_uniformOn
#check @«2606.16671v2».SineJacobi.greenProfile_eLpNorm_limit
#check @«2606.16671v2».SineJacobi.endpoint_product_sum_limit
#check @«2606.16671v2».SineJacobi.endpoint_product_square_sum_limit

/-!
2606.16671v2, Lemma E.4. Finite sine-lattice endpoint product asymptotics.
-/
#check @«2606.16671v2».SineJacobi.ratio_scaled_limit
#check @«2606.16671v2».SineJacobi.convolutionIntegral_limit
#check @«2606.16671v2».SineJacobi.convolutionIntegral_eq_elliptic
#check @«2606.16671v2».SineJacobi.endpointProfile_uniformOn
#check @«2606.16671v2».SineJacobi.greenProfile_eLpNorm_limit
#check @«2606.16671v2».SineJacobi.endpoint_product_sum_limit
#check @«2606.16671v2».SineJacobi.endpoint_product_square_sum_limit

/-!
2606.16671v2, Lemma E.5. Persymmetric inverse-spectral criterion.
-/
#check @«2606.16671v2».JacobiData.spectral_weight_cofactor
#check @«2606.16671v2».JacobiData.spectral_endpoint_product
#check @«2606.16671v2».JacobiData.block_pair_unique
#check @«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights

/-!
2606.16671v2, Lemma E.6. Symmetry and final polynomial of the sine matrix.
-/
#check @«2606.16671v2».SineJacobi.matrix_persymmetric
#check @«2606.16671v2».SineJacobi.spectral_weight
#check @«2606.16671v2».SineJacobi.terminal

/-!
2606.16671v2, Lemma E.7. Positive normalization outside the Jacobi spectrum.
-/
#check @«2606.16671v2».JacobiData.block_eval_pos_of_spectrum
#check @«2606.16671v2».JacobiData.admissible_of_spectrum
#check @«2606.16671v2».SineJacobi.admissible

/-!
2606.16671v2, Lemma E.8. Nonnegative Fourier coefficients and endpoint maxima for every block.
-/
#check @«2606.16671v2».Continuant.interior_identity
#check @«2606.16671v2».SineJacobi.blockFourier_interior_nonneg
#check @«2606.16671v2».SineJacobi.endpointMax

/-!
2606.16671v2, Appendix F. Additional numerical experiments. Omitted: Experimental outputs are
outside the mathematical proof scope.
-/

