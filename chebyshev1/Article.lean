import chebyshev1

/-!
Article: chebyshev1 — statements in the order of the article.
Use: imported by `Check`; all references below are type-checked, and their proof bodies
are included in its module-owned axiom audit. Comments explain numerical exclusions.
The showcase introduces no additional mathematical hypotheses.
-/

/-!
chebyshev1, Lemma 1.1. First-order expansion of the transfer.
-/
#check @chebyshev1.Realization.hasDerivAt_operatorTransfer
#check @chebyshev1.Realization.linearResponse_eq_sum
#check @chebyshev1.Realization.spectralPair_linearResponse
#check @chebyshev1.Realization.linearResponse_coordinates

/-!
chebyshev1, Definition 1.2. Realizations, kernels and Hessian-drift gain.
-/
#check @chebyshev1.Realization
#check @chebyshev1.Realization.scalarStep
#check @chebyshev1.Realization.operatorTransfer
#check @chebyshev1.Realization.residualPolynomial
#check @chebyshev1.Realization.kernel
#check @chebyshev1.Realization.kernelNorm
#check @chebyshev1.Realization.gain

/-!
chebyshev1, Proposition 1.3. Finite expansion, Hilbert–Schmidt bound and sharpness.
-/
#check @chebyshev1.orderedProduct_add_expansion
#check @chebyshev1.insertionMultilinear
#check @chebyshev1.Realization.finiteDrift_polynomial_decomposition
#check @chebyshev1.Realization.operatorTransfer_affine_by_degree
#check @chebyshev1.Realization.hsNorm_linearResponse_bound
#check @chebyshev1.Realization.hs_bound_attained
#check @chebyshev1.Realization.hs_constant_minimal
#check @chebyshev1.Realization.gain_attained

/-!
chebyshev1, Theorem 1.4. Sharp stepsize drift lower bound and asymptotics.
-/
#check @chebyshev1.Stepsize.endpoint_square_sum
#check @chebyshev1.Stepsize.gain_lower_bound
#check @chebyshev1.Stepsize.correction_error_isBigO
#check @chebyshev1.Stepsize.lowerBound_asymptotic

/-!
chebyshev1, Theorem 2.1. Prefix-exact recurrence and quadratic transfer.
-/
#check @chebyshev1.Prefix.residualPolynomial_eq
#check @chebyshev1.Prefix.operator_exact
#check @chebyshev1.Prefix.quadraticError_exact
#check @chebyshev1.Prefix.quadraticError_eq_transfer

/-!
chebyshev1, Theorem 2.2. Exact prefix kernel, gain and asymptotics.
-/
#check @chebyshev1.Prefix.kernel_zero
#check @chebyshev1.Prefix.kernel_succ
#check @chebyshev1.Prefix.gain_exact
#check @chebyshev1.Prefix.gain_exact_sum
#check @chebyshev1.Prefix.gain_isEquivalent_rpow

/-!
chebyshev1, Theorem 3.1. Optimality among causal two-term prefix methods.
-/
#check @chebyshev1.TwoTerm.kernel_eq_prefix
#check @chebyshev1.TwoTerm.gain_eq_prefix
#check @chebyshev1.TwoTerm.optimal_gain
#check @chebyshev1.TwoTerm.standard_attains
#check @chebyshev1.TwoTerm.optimal_asymptotic

/-!
chebyshev1, Theorem 4.1. Jacobi recurrence, fixed point and terminal exactness.
-/
#check @chebyshev1.JacobiData.fixed_point
#check @chebyshev1.JacobiData.quadraticError_exact
#check @chebyshev1.JacobiData.terminal_exact

/-!
chebyshev1, Theorem 4.2. Block determinants, first-variation kernel and gain.
-/
#check @chebyshev1.JacobiData.block_eq_charpoly
#check @chebyshev1.JacobiData.matrix_principal_block
#check @chebyshev1.JacobiData.kernel_eq
#check @chebyshev1.JacobiData.kernelNorm_eq_blocks
#check @chebyshev1.JacobiData.gain_eq_blocks

/-!
chebyshev1, Theorem 4.3. All insertion orders, partition bounds, finite/cosh bounds and
attainment.
-/
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

/-!
chebyshev1, Corollary 4.4. Attained finite-drift bounds for the prefix recurrence.
-/
#check @chebyshev1.Prefix.opNorm_linearResponse_le
#check @chebyshev1.Prefix.opNorm_finiteDrift_le
#check @chebyshev1.Prefix.opNorm_driftRemainder_le
#check @chebyshev1.Prefix.opNorm_driftRemainder_cosh_le
#check @chebyshev1.Prefix.static_shift_attained

/-!
chebyshev1, Algorithm 1. Explicit prefix-exact gradient recurrence.
-/
#check @chebyshev1.Prefix.algorithmStep_succ
#check @chebyshev1.Prefix.beta_coefficient
#check @chebyshev1.Prefix.realization
#check @chebyshev1.Prefix.scalarStep_zero

/-!
chebyshev1, Algorithm 2. Explicit sine–Jacobi gradient recurrence.
-/
#check @chebyshev1.SineJacobi.method_initial
#check @chebyshev1.SineJacobi.method_coefficients
#check @chebyshev1.SineJacobi.quadraticError_exact

/-!
chebyshev1, Theorem 5.1. Endpoint-profile L2 convergence and limiting Green energy.
-/
#check @chebyshev1.SineJacobi.sineIntegral_eq
#check @chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit
#check @chebyshev1.SineJacobi.greenWeight_energy_limit

/-!
chebyshev1, Theorem 5.2. Exact sine gain, resolvent expression, asymptotics and energy value.
-/
#check @chebyshev1.SineJacobi.gain_exact
#check @chebyshev1.SineJacobi.gain_exact_resolvent
#check @chebyshev1.SineJacobi.resolvent_trace
#check @chebyshev1.SineJacobi.gain_isEquivalent
#check @chebyshev1.SineJacobi.gain_eventually_lt_prefix
#check @chebyshev1.SineJacobi.sineEnergy
#check @chebyshev1.SineJacobi.sineEnergy_ge_one
#check @chebyshev1.SineJacobi.sineEnergy_le_four_div_pi
#check @chebyshev1.SineJacobi.sineEnergy_lt_four_thirds
#check @chebyshev1.SineJacobi.sineEnergy_decimal
#check @chebyshev1.SineJacobi.sineEnergy_rounding

/-!
chebyshev1, Corollary 5.3. Attained finite-drift bounds for the sine chain.
-/
#check @chebyshev1.SineJacobi.G_exact
#check @chebyshev1.SineJacobi.opNorm_linearResponse_le
#check @chebyshev1.SineJacobi.opNorm_finiteDrift_le
#check @chebyshev1.SineJacobi.opNorm_driftRemainder_le
#check @chebyshev1.SineJacobi.opNorm_driftRemainder_cosh_le
#check @chebyshev1.SineJacobi.static_shift_attained
#check @chebyshev1.SineJacobi.driftOrder_static_attained

/-!
chebyshev1, Corollary 5.4. Lipschitz-Hessian error bound for both methods.
-/
#check @chebyshev1.Nonlinear.averagedDerivative_apply
#check @chebyshev1.Nonlinear.averagedDerivative_sub_norm_le
#check @chebyshev1.Nonlinear.lipschitzHessian_error_le

/-!
chebyshev1, Remark 5.5. Exact drift scale, accuracy asymptotics and rational finite examples.
-/
#check @chebyshev1.SpectralInterval.amplification_cosh
#check @chebyshev1.SpectralInterval.amplification_effectiveKappa_le
#check @chebyshev1.SpectralInterval.drift_scale_limit
#check @chebyshev1.SpectralInterval.drift_factor_limit
#check @chebyshev1.SpectralInterval.logarithmic_drift_scale_limit
#check @chebyshev1.Realization.static_shift_at_mu
#check @chebyshev1.terminal_log_accuracy_ratio_limit
#check @chebyshev1.low_accuracy_amplification_ratio_limit
#check @chebyshev1.terminal_certificate
#check @chebyshev1.amplification_certificate_one_percent
#check @chebyshev1.amplification_certificate_five_percent
#check @chebyshev1.amplification_certificate_quarter

/-!
chebyshev1, Section 6. Performance experiments. Omitted: Experimental runs and measured
performance are outside the mathematical proof scope.
-/

/-!
chebyshev1, Appendix A. Proofs of Lemma 1.1, Proposition 1.3 and Theorem 1.4.
-/
#check @chebyshev1.Realization.hasDerivAt_operatorTransfer
#check @chebyshev1.Realization.linearResponse_eq_sum
#check @chebyshev1.Realization.spectralPair_linearResponse
#check @chebyshev1.Realization.linearResponse_coordinates
#check @chebyshev1.orderedProduct_add_expansion
#check @chebyshev1.insertionMultilinear
#check @chebyshev1.Realization.finiteDrift_polynomial_decomposition
#check @chebyshev1.Realization.operatorTransfer_affine_by_degree
#check @chebyshev1.Realization.hsNorm_linearResponse_bound
#check @chebyshev1.Realization.hs_bound_attained
#check @chebyshev1.Realization.hs_constant_minimal
#check @chebyshev1.Realization.gain_attained
#check @chebyshev1.Stepsize.endpoint_square_sum
#check @chebyshev1.Stepsize.gain_lower_bound
#check @chebyshev1.Stepsize.correction_error_isBigO
#check @chebyshev1.Stepsize.lowerBound_asymptotic

/-!
chebyshev1, Lemma B.1. Chebyshev tail fundamental solution.
-/
#check @chebyshev1.Prefix.tail_column
#check @chebyshev1.Prefix.tail_fundamental

/-!
chebyshev1, Theorem C.1. Local uniqueness of the causal two-term realization.
-/
#check @chebyshev1.TwoTerm.local_unique
#check @chebyshev1.TwoTerm.coefficients_unique_explicit

/-!
chebyshev1, Appendix D. Proofs of the Jacobi block and all-order drift identities.
-/
#check @chebyshev1.JacobiData.fixed_point
#check @chebyshev1.JacobiData.quadraticError_exact
#check @chebyshev1.JacobiData.terminal_exact
#check @chebyshev1.JacobiData.block_eq_charpoly
#check @chebyshev1.JacobiData.matrix_principal_block
#check @chebyshev1.JacobiData.kernel_eq
#check @chebyshev1.JacobiData.kernelNorm_eq_blocks
#check @chebyshev1.JacobiData.gain_eq_blocks
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

/-!
chebyshev1, Theorem E.1. Sine-lattice couplings, spectrum, expansion and symmetry.
-/
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

/-!
chebyshev1, Lemma E.2. Root-of-unity Rogers recurrence, Fourier coefficients and orthogonality.
-/
#check @chebyshev1.SineJacobi.rogers_recurrence
#check @chebyshev1.SineJacobi.rogers_terminal
#check @chebyshev1.SineJacobi.normalized_fourier
#check @chebyshev1.SineJacobi.normalizedCoefficient_sum
#check @chebyshev1.SineJacobi.leading_orthogonality
#check @chebyshev1.SineJacobi.leading_norm_positive

/-!
chebyshev1, Theorem E.3. Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
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

/-!
chebyshev1, Lemma E.4. Finite sine-lattice endpoint product asymptotics.
-/
#check @chebyshev1.SineJacobi.ratio_scaled_limit
#check @chebyshev1.SineJacobi.convolutionIntegral_limit
#check @chebyshev1.SineJacobi.convolutionIntegral_eq_elliptic
#check @chebyshev1.SineJacobi.endpointProfile_uniformOn
#check @chebyshev1.SineJacobi.greenProfile_eLpNorm_limit
#check @chebyshev1.SineJacobi.endpoint_product_sum_limit
#check @chebyshev1.SineJacobi.endpoint_product_square_sum_limit

/-!
chebyshev1, Lemma E.5. Persymmetric inverse-spectral criterion.
-/
#check @chebyshev1.JacobiData.spectral_weight_cofactor
#check @chebyshev1.JacobiData.spectral_endpoint_product
#check @chebyshev1.JacobiData.block_pair_unique
#check @chebyshev1.JacobiData.persymmetric_iff_spectral_weights

/-!
chebyshev1, Lemma E.6. Symmetry and final polynomial of the sine matrix.
-/
#check @chebyshev1.SineJacobi.matrix_persymmetric
#check @chebyshev1.SineJacobi.spectral_weight
#check @chebyshev1.SineJacobi.terminal

/-!
chebyshev1, Lemma E.7. Positive normalization outside the Jacobi spectrum.
-/
#check @chebyshev1.JacobiData.block_eval_pos_of_spectrum
#check @chebyshev1.JacobiData.admissible_of_spectrum
#check @chebyshev1.SineJacobi.admissible

/-!
chebyshev1, Lemma E.8. Nonnegative Fourier coefficients and endpoint maxima for every block.
-/
#check @chebyshev1.Continuant.interior_identity
#check @chebyshev1.SineJacobi.blockFourier_interior_nonneg
#check @chebyshev1.SineJacobi.endpointMax

/-!
chebyshev1, Appendix F. Additional numerical experiments. Omitted: Experimental outputs are
outside the mathematical proof scope.
-/

