import jacobi

/-!
Article: jacobi — statements and labeled proof ingredients in source order.
Use: Check imports this showcase and audits the entire mathematical library.
Each #check checks an existing declaration, whose proof is included in the audit.
Coverage is recorded in ArticleMap.md. Alternative proof entries explain
which auxiliary source argument is replaced by the checked direct proof.
Decimal numerical illustrations are intentionally excluded.
-/

/-!
jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proved.
-/
#check @jacobi.Finite.persymmetricFiber_symmetric
#check @jacobi.Finite.symmetric_weights
#check @jacobi.Finite.exists_unique_persymmetric

/-!
jacobi, Proposition 1.1. Criticality
Proved.
-/
#check @jacobi.Finite.logFiber_zero
#check @jacobi.Finite.fderiv_even_zero
#check @jacobi.Finite.persymmetric_critical

/-!
jacobi, Proposition 1.2. Energy and endpoint drift
Proved.
-/
#check @jacobi.Applications.general_drift_kernel
#check @jacobi.Applications.general_drift_endpoint
#check @jacobi.Applications.general_drift_endpoint_norm
#check @jacobi.Applications.general_drift_gain_lower
#check @jacobi.Applications.endpoint_kernel
#check @jacobi.Applications.endpoint_kernel_green
#check @jacobi.Applications.endpoint_gain_energy
#check @jacobi.Applications.block_endpoint_square

/-!
jacobi, Lemma 1.3. Spectral convergence
Proved.
-/
#check @jacobi.Jacobi.nonnegative_scheffe
#check @jacobi.Jacobi.finiteLambdaAt_l1_tendsto
#check @jacobi.Jacobi.finiteEigenvalue_eq
#check @jacobi.Jacobi.fibre_spectral_limit
#check @jacobi.Jacobi.arbitrary_fibre_spectral_limit

/-!
jacobi, Theorem 2.1. Canonical limit
Proved: the full self-adjoint spectral operator acts classically on every compact interior C2 test and distributionally on its entire spectral domain; all stated canonical finite limits hold.
-/
#check @jacobi.Comparison.target_energy_limit
#check @jacobi.Comparison.target_diagonal_floor_limit
#check @jacobi.Comparison.scaledTargetGreen_uniform
#check @jacobi.Comparison.scaledTargetDiagonal_uniform
#check @jacobi.Comparison.scaledTargetDiagonal_bound
#check @jacobi.Comparison.finiteNuclearGreen_operator
#check @jacobi.Comparison.embeddedGreenOperator_trace_limit
#check @jacobi.Comparison.embeddedGreenOperator_difference_traceClass
#check @jacobi.GelfandLevitan.targetOperator_domain
#check @jacobi.GelfandLevitan.targetOperator_selfAdjoint
#check @jacobi.GelfandLevitan.targetOperator_nonnegative
#check @jacobi.GelfandLevitan.finiteTargetWave_second_derivative
#check @jacobi.GelfandLevitan.finiteTargetWave_equation
#check @jacobi.GelfandLevitan.targetOperator_differential
#check @jacobi.GelfandLevitan.targetOperator_eigenvalue_iff
#check @jacobi.GelfandLevitan.targetOperator_eigenvector_simple
#check @jacobi.GelfandLevitan.targetOperator_strictPositive
#check @jacobi.GelfandLevitan.fullWaveMap_half
#check @jacobi.GelfandLevitan.fullWaveMap_reflection
#check @jacobi.GelfandLevitan.targetPotential_half
#check @jacobi.GelfandLevitan.diagonalPhysicalSlope_strip
#check @jacobi.GelfandLevitan.targetPotential_strip
#check @jacobi.GelfandLevitan.targetGreenKernel_uniform_limit
#check @jacobi.GelfandLevitan.targetGreenKernel_symmetric
#check @jacobi.GelfandLevitan.targetGreen_diagonal
#check @jacobi.GelfandLevitan.targetOperator_compact_test
#check @jacobi.GelfandLevitan.targetOperator_weak_action
#check @jacobi.GelfandLevitan.targetGreen_test_identity

/-!
jacobi, Proposition 2.2. The Green coordinate
Proved: the original kernel has the exact exponential coordinate formula; the actual packed density has the entire prescribed spectrum with multiplicities and all three stated integrals. The spectral proof uses transferred orthonormal eigenfunctions and equality of the positive trace.
-/
#check @jacobi.Trichotomy.targetGreen_pos
#check @jacobi.Trichotomy.target_pencil_posDef
#check @jacobi.Trichotomy.targetGreen_nonneg
#check @jacobi.Trichotomy.targetGreen_markov
#check @jacobi.Trichotomy.packedDensity_mass
#check @jacobi.Trichotomy.packedDensity_root_mass
#check @jacobi.Trichotomy.packedDensity_energy
#check @jacobi.Trichotomy.packingCoordinate_reflection
#check @jacobi.Trichotomy.packingImage_ordConnected
#check @jacobi.Trichotomy.packingImage_open
#check @jacobi.Trichotomy.targetGreen_column_model
#check @jacobi.Trichotomy.targetGreen_local_factors
#check @jacobi.Trichotomy.targetGreen_exponential
#check @jacobi.Trichotomy.packedBasis_orthonormal
#check @jacobi.Trichotomy.packedKernel_basis
#check @jacobi.Trichotomy.packedDensity_spectrum

/-!
jacobi, Proposition 3.1. Resolvent packing
Proved.
-/
#check @jacobi.Packing.spectral_distance
#check @jacobi.Packing.density_formula
#check @jacobi.Packing.volume_identities
#check @jacobi.Packing.density_properties
#check @jacobi.Packing.packed_spectral_mass

/-!
jacobi, Section 3.2 (sharp Young inequality).
Proved.
-/
#check @jacobi.Young.sharp_young_general_eq_iff
#check @jacobi.Young.EnergySource.energy_pos_of_not_ae_zero
#check @jacobi.Young.sharp_young_complete

/-!
jacobi, Equation (3.3) (exact U density and full spectrum).
Proved.
-/
#check @jacobi.Young.distinguished_spectrum
#check @jacobi.Young.distinguished_spectrum_simple
#check @jacobi.Young.distinguished_admissible
#check @jacobi.Young.joint_upper_at_U
#check @jacobi.Young.joint_calibration_at_U

/-!
jacobi, Section 3.2 (sharp comparison at U).
Proved.
-/
#check @jacobi.Comparison.jacobiOptimalEnergy_bounds
#check @jacobi.Comparison.young_le_lowerConstant
#check @jacobi.Comparison.jacobiOptimalEnergy_U

/-!
jacobi, Equation (3.5) (regularized Fredholm functional).
Proved.
-/
#check @jacobi.Variational.fredholmTerm_series
#check @jacobi.Variational.fredholmSpectrum_series
#check @jacobi.Variational.L1Source.fredholm_series
#check @jacobi.Variational.fredholm_mono_of_moments
#check @jacobi.Variational.Density.fredholm_mono
#check @jacobi.Variational.L1Source.fredholm_second_lower

/-!
jacobi, Section 3.5 (edge data and the lower constant).
Proved.
-/
#check @jacobi.Variational.Density
#check @jacobi.Variational.EdgeSpectrum
#check @jacobi.Variational.EdgeSpectrum.second_lt_mass_sq
#check @jacobi.Variational.EdgeSpectrum.second_pos
#check @jacobi.Variational.lowerConstant_transfer

/-!
jacobi, Theorem 3.2. Lower bound for general edge data
Proved.
-/
#check @jacobi.Variational.EdgeSpectrum.second_pos
#check @jacobi.Variational.lowerConstant_transfer

/-!
jacobi, Theorem 4.1. Two-sided estimate
Proved.
-/
#check @jacobi.Comparison.realOptimalEnergy_definition
#check @jacobi.Comparison.realOptimalEnergy_bounds
#check @jacobi.Comparison.realOptimalEnergy_U

/-!
jacobi, Theorem 4.2. Analyticity and contact
Proved.
-/
#check @jacobi.Analytic.originalOptimalEnergy_uniform_upper
#check @jacobi.Analytic.originalOptimalEnergy_hasDerivAt_U
#check @jacobi.Analytic.theorem_C

/-!
jacobi, Theorem 5.1. Sharp Nesterov and block gains
Proved.
-/
#check @jacobi.Applications.nesterov_kernel
#check @jacobi.Applications.nesterov_kernel_le_endpoint
#check @jacobi.Applications.nesterov_gain_eq_endpoint
#check @jacobi.Applications.nesterov_gain_square
#check @jacobi.Applications.uniformU_even_block_gain_square
#check @jacobi.Applications.endpoint_gain_limit
#check @jacobi.Applications.block_optimal_gain_limit
#check @jacobi.Applications.canonical_block_gain_ratio
#check @jacobi.Applications.u_fibre_transfer
#check @jacobi.Applications.block_terminal_nesterov
#check @jacobi.Applications.block_terminal_polynomial

/-!
jacobi, Lemma 5.2 (Closed fibres).
Positive prefixes, zero-link restarts, the full drift identity, transfer and attained closed-
fibre minima. Proved.
-/
#check @jacobi.Finite.ClosedNodes.prefix_pos
#check @jacobi.Finite.ClosedNodes.prefix_exact
#check @jacobi.Finite.ClosedNodes.restart_iff
#check @jacobi.Finite.ClosedNodes.endpoint_gain_square
#check @jacobi.Applications.closed_general_drift_kernel
#check @jacobi.Applications.closed_general_drift_endpoint_norm
#check @jacobi.Variational.closed_lowerConstant_transfer
#check @jacobi.Finite.ClosedNodes.exists_minimizer

/-!
jacobi, Theorem 5.3 (All three-term realizations).
The full repeated-root spectrum, homogeneous lower bound and sharp symmetric minimum, with
canonical attaining blocks in both parities. Proved. The Lean minimum is normalized by the cube
of the full horizon.
-/
#check @jacobi.Applications.closedEndpointMinimum_attained
#check @jacobi.Applications.nesterov_restarts_necessary
#check @jacobi.Applications.nesterov_closed_terminal
#check @jacobi.Applications.nesterovClosed_spectral_limit
#check @jacobi.Variational.closed_quarter_lowerConstant_transfer
#check @jacobi.Applications.nesterov_all_three_term_lower
#check @jacobi.Applications.nesterov_canonical_block_limit
#check @jacobi.Applications.nesterov_closed_sharp_limit

/-!
jacobi, Theorem 5.4 (The standard one-sided limit).
Normalized Gauss weights, the conductance formula (5.9), coefficient limits (5.10), the uniform
kernel with terminal zero extension, global bound and exact cubic energy. Proved by moving-mesh
limits and domination.
-/
#check @jacobi.Jacobi.standardChain_inFiber
#check @jacobi.Jacobi.standardGauss_exact
#check @jacobi.Jacobi.standard_diagonal_mass
#check @jacobi.Jacobi.standard_green_entry
#check @jacobi.Applications.standard_kernel_uniform
#check @jacobi.Jacobi.standardGreenTail_normalized_bound
#check @jacobi.Applications.standard_realization_energy
#check @jacobi.Applications.standard_fibre_upper_bound

/-!
jacobi, Proposition 5.5 (Resolvent flow).
The global actual weight flow, Lax equation, conserved trace, exact derivative and both
derivative bounds (5.12), Taylor estimate (5.13), and both sorted matrix limits. Proved.
-/
#check @jacobi.Finite.resolventFlow_weights
#check @jacobi.Finite.resolventWeights_formula
#check @jacobi.Finite.resolventFlow_charpoly
#check @jacobi.Finite.resolventFlow_trace
#check @jacobi.Finite.resolventFlow_lax
#check @jacobi.Finite.resolventFlow_generator
#check @jacobi.Finite.flowEnergyVelocity_pairs
#check @jacobi.Finite.flowEnergyVelocity_abs_le
#check @jacobi.Finite.flowEnergyAcceleration_abs_le
#check @jacobi.Finite.flowEnergy_taylor
#check @jacobi.Finite.resolventFlow_atTop
#check @jacobi.Finite.resolventFlow_atBot

/-!
jacobi, Theorem 5.6 (Strict improvement).
Exact D_alpha, including alpha zero; eventual noncriticality; the explicit time and gap for
genuine flowed competitors and the finite-fibre optimum. Proved.
-/
#check @jacobi.Jacobi.standard_slope_integral
#check @jacobi.Applications.standard_initial_slope_limit
#check @jacobi.Applications.standard_eventually_noncritical
#check @jacobi.Applications.standard_flow_descent
#check @jacobi.Applications.standard_fibre_descent
#check @jacobi.Applications.jacobiOptimalEnergy_standard_descent

/-!
jacobi, Corollary 5.7 (Optimal endpoint comparison).
The entire ratio sandwich, strict upper bound below two away from b=1, and convergence to two at
b=1. Proved. Positive-link blocks use an infimum; the full closed class has an attained minimum.
-/
#check @jacobi.Applications.nesterov_young_ratio_lower
#check @jacobi.Applications.nesterov_ratio_sandwich
#check @jacobi.Applications.nesterov_block_ratio_lt_two
#check @jacobi.Applications.nesterov_symmetric_ratios

/-!
jacobi, Section 5.6 (Orbit geometry and limiting energy).
Finite-time transitivity of the two-root fibre, the energies of both sorted Richardson limits
and their quartic Jacobi asymptotic. Proved.
-/
#check @jacobi.Finite.resolventFlow_two_point_surjective
#check @jacobi.Finite.resolventFlow_energy_atTop
#check @jacobi.Finite.resolventFlow_energy_atBot
#check @jacobi.Finite.richardsonEnergy_jacobi_limit

/-!
jacobi, Figure 2. Numerical illustration of the resolvent flow.
The sampled coordinates, Lanczos rounding and plotted percentage are
illustrative computations, excluded from formal certification. The flow,
its derivatives, matrix sorting and limiting energies are proved above.
-/

/-!
jacobi, Proposition 6.1. The same spectrum, different optimal energies
Proved.
-/
#check @jacobi.Counterexample.identical_edges_different_energies
#check @jacobi.Counterexample.edge_calibration_not_sharp
#check @jacobi.Counterexample.counterexample_packing_rootMass
#check @jacobi.Counterexample.u_base_energy_limit
#check @jacobi.Counterexample.u_fibre_energy_limit
#check @jacobi.Counterexample.u_polynomial_energy_limit
#check @jacobi.Counterexample.laguerre_polynomial_minimum
#check @jacobi.Counterexample.laguerre_polynomial_infimum
#check @jacobi.Counterexample.laguerre_polynomial_minimum_limit

/-!
jacobi, Section 6 (bidiagonal swap identity).
Proved.
-/
#check @jacobi.Counterexample.constant_drift_diagonal_ne
#check @jacobi.Counterexample.swapped_inverse_diagonal
#check @jacobi.Counterexample.swapped_posDef

/-!
jacobi, Proposition A.1. The Nesterov hard edge
Proved.
-/
#check @jacobi.Applications.nesterov_original_residual
#check @jacobi.Applications.nesterov_original_hard_edge_uniform
#check @jacobi.Applications.nesterov_original_small_zero_iff
#check @jacobi.Applications.nesterov_original_small_zero_simple
#check @jacobi.Applications.nesterov_original_operator
#check @jacobi.Applications.nesterov_all_hard_edge_uniform
#check @jacobi.Applications.nesterov_all_small_zero_limit
#check @jacobi.Applications.linearIterates_eq_aeval
#check @jacobi.Applications.landweber_linear_iterate
#check @jacobi.Applications.nesterov_linear_terminal_realization

/-!
jacobi, Lemma A.2. The original endpoint gain for general momentum
Proved.
-/
#check @jacobi.Applications.endpoint_gain_limit

/-!
jacobi, Proposition B.1. Uniform two-edge zero estimates
Proved.
-/
#check @jacobi.Jacobi.pairIndex_comm
#check @jacobi.Jacobi.zeros_estimates

/-!
jacobi, Lemma C.1. Reference data
Proved.
-/
#check @jacobi.ComplexReference.reference_gegenbauer
#check @jacobi.ComplexReference.reference_compact_strip_bounds
#check @jacobi.ComplexReference.referenceNormIntegral_real
#check @jacobi.ComplexReference.referenceNormIntegral_eq
#check @jacobi.ComplexReference.reference_norm_integral
#check @jacobi.ComplexReference.scaledNorming_norm
#check @jacobi.ComplexReference.scaledNorming_ne_zero
#check @jacobi.ComplexReference.norming_bounds
#check @jacobi.Reference.norming_asymptotic
#check @jacobi.Reference.norming_bounds
#check @jacobi.ComplexReference.wave_global_endpoint_uniform
#check @jacobi.ComplexReference.wave_energy_derivative_uniform
#check @jacobi.ComplexReference.sharp_wave_deriv_uniform
#check @jacobi.ComplexReference.scaled_complex_energy_disk
#check @jacobi.ComplexReference.sharp_energy_deriv_low_uniform
#check @jacobi.ComplexReference.sharp_energy_derivative_uniform
#check @jacobi.ComplexReference.norming_asymptotic_uniform

/-!
jacobi, Appendix C.1 (sharp reference-frequency bounds).
Alternative proof: the actual sharp reference-wave and derivative bounds are proved directly by the differential equation and energy propagation; the source auxiliary repeated-integration-by-parts route is replaced.
-/
#check @jacobi.ComplexReference.wave_global_endpoint_uniform
#check @jacobi.ComplexReference.wave_energy_derivative_uniform
#check @jacobi.ComplexReference.sharp_wave_deriv_uniform
#check @jacobi.ComplexReference.scaled_complex_energy_disk
#check @jacobi.ComplexReference.sharp_energy_deriv_low_uniform
#check @jacobi.ComplexReference.sharp_energy_derivative_uniform

/-!
jacobi, Appendix C.1 (selected endpoint branch).
Alternative proof for the required branch: the chosen normalized analytic solution, its endpoint derivative and Wronskian, and all actual reference Green identities are proved directly.
-/
#check @jacobi.Reference.Hypergeometric.euler_power_derivative
#check @jacobi.Reference.Hypergeometric.gauss_zero_unique
#check @jacobi.Reference.solutionSlope_factor
#check @jacobi.Reference.referenceWronskian_zero
#check @jacobi.Reference.reference_green_identity

/-!
jacobi, Appendix C.1 (negative-energy bounds).
Proved.
-/
#check @jacobi.Reference.solution_negative_upper
#check @jacobi.Reference.wave_imaginary_lower
#check @jacobi.Reference.solution_negative_lower
#check @jacobi.Reference.weightedSlopeDefect_hasDerivAt
#check @jacobi.Reference.negativeSlopeDefect_integral
#check @jacobi.Reference.negativeSlopeDefect_quarter_bound

/-!
jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proved.
-/
#check @jacobi.Reference.midpointScalar_eq
#check @jacobi.Reference.wave_midpoint_formula
#check @jacobi.Reference.waveSlope_midpoint_formula
#check @jacobi.Reference.characteristicTau_negative_asymptotic
#check @jacobi.Reference.characteristicTau_real
#check @jacobi.Reference.characteristicTau_negative_complex_asymptotic
#check @jacobi.Reference.characteristicSigma_shifted_negative_ne_zero
#check @jacobi.Reference.relative_characteristic_negative_rate
#check @jacobi.Reference.relative_characteristic_negative_scaled_error

/-!
jacobi, Proposition C.2. Spectral reconstruction
Proved.
-/
#check @jacobi.GelfandLevitan.triangleKernel_satisfiesGL
#check @jacobi.GelfandLevitan.triangleKernel_unique
#check @jacobi.GelfandLevitan.GL_exists_unique
#check @jacobi.GelfandLevitan.kernelDiagonal_contDiffOn_strip
#check @jacobi.GelfandLevitan.kernelDiagonal_contDiffOn
#check @jacobi.GelfandLevitan.midpointRowEvaluation_wave
#check @jacobi.GelfandLevitan.midpoint_dirichlet_kernel_row
#check @jacobi.GelfandLevitan.kernelDiagonal_midpoint_zero
#check @jacobi.GelfandLevitan.fullTransformedVector_orthogonal_eq_bot
#check @jacobi.GelfandLevitan.fullTargetBasis_apply
#check @jacobi.GelfandLevitan.fullTargetBasis_reflection
#check @jacobi.GelfandLevitan.targetGreenActionMap_inner
#check @jacobi.GelfandLevitan.targetGreenActionMap_toLp
#check @jacobi.GelfandLevitan.targetGreen_integral_action

/-!
jacobi, Appendix C.2 (norming ratios).
Proved.
-/
#check @jacobi.Reference.normingRatio_exponential_error
#check @jacobi.Reference.harmonic_log_comparison
#check @jacobi.Reference.normingRatio_asymptotic

/-!
jacobi, Appendix C.2 (uniform GL coercivity).
Proved.
-/
#check @jacobi.GelfandLevitan.positiveOperator_coercive
#check @jacobi.GelfandLevitan.quadratic_coercive
#check @jacobi.GelfandLevitan.quadratic_coercive_all_intervals

/-!
jacobi, Appendix C.2 (gL equation, uniqueness and continuity).
Proved.
-/
#check @jacobi.GelfandLevitan.triangleKernel_satisfiesGL
#check @jacobi.GelfandLevitan.triangleKernel_unique
#check @jacobi.GelfandLevitan.GL_exists_unique

/-!
jacobi, Appendix C.2 (exact parity splitting).
Proved.
-/
#check @jacobi.GelfandLevitan.signed_kernel_summable
#check @jacobi.GelfandLevitan.parity_splitting
#check @jacobi.GelfandLevitan.parity_splitting_tsum

/-!
jacobi, Appendix C.2 (two transformed orthonormal bases).
Proved.
-/
#check @jacobi.GelfandLevitan.transformedParityBasis_apply
#check @jacobi.GelfandLevitan.normalizedTransformedVector_parity_inner
#check @jacobi.GelfandLevitan.transformedVector_parity_orthogonal

/-!
jacobi, Appendix C.2 (green part and regularized kernel series).
Proved.
-/
#check @jacobi.GelfandLevitan.realSolution_hasDerivAt
#check @jacobi.GelfandLevitan.regularizedTerm_hasDerivAt
#check @jacobi.GelfandLevitan.regularizedSlopeTerm_decomposition
#check @jacobi.GelfandLevitan.regularizedSlope_absolute_summable
#check @jacobi.GelfandLevitan.regularizedSlope_uniform_limit
#check @jacobi.GelfandLevitan.regularizedSlope_continuousOn

/-!
jacobi, Appendix C.2 (transformation-kernel regularity).
Proved.
-/
#check @jacobi.GelfandLevitan.kernelDiagonal_contDiffOn_strip
#check @jacobi.GelfandLevitan.kernelDiagonal_contDiffOn

/-!
jacobi, Appendix C.2 (transformed ODE and Green identity).
Proved.
-/
#check @jacobi.GelfandLevitan.stripComplex_apply
#check @jacobi.GelfandLevitan.transformedDiagonalStrip_hasDerivWithinAt
#check @jacobi.GelfandLevitan.transformedSolution_ODE_strip
#check @jacobi.GelfandLevitan.fullWavePhysical_second_derivative
#check @jacobi.GelfandLevitan.fullWavePhysical_equation
#check @jacobi.GelfandLevitan.fullWavePhysical_eq_map

/-!
jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proved.
-/
#check @jacobi.Support.coefficientC_pos
#check @jacobi.Support.coefficientC_zero
#check @jacobi.Support.coefficientA_terminal

/-!
jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proved.
-/
#check @jacobi.Support.naturalChain_inFiber
#check @jacobi.Support.naturalChain_spectrum
#check @jacobi.Support.naturalChain_canonical
#check @jacobi.Support.naturalChain_coupling_reflection
#check @jacobi.Support.naturalChain_reverse
#check @jacobi.Support.naturalChain_persymmetric
#check @jacobi.Support.supportBasis_values
#check @jacobi.Support.supportChain_charpoly
#check @jacobi.Support.supportChain_spectrum

/-!
jacobi, Appendix C.3 (sine-product estimates).
Proved.
-/
#check @jacobi.Support.sineProduct_zero
#check @jacobi.Support.sineProduct_succ
#check @jacobi.Support.sineProduct_pos

/-!
jacobi, Appendix C.3 (top-node polynomials).
Proved.
-/
#check @jacobi.Support.topValue_uniform
#check @jacobi.Support.topValue_difference

/-!
jacobi, Appendix C.3 (coefficient bounds).
Proved.
-/
#check @jacobi.Support.coefficient_bounds

/-!
jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proved.
-/
#check @jacobi.Support.volterra_estimates

/-!
jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proved.
-/
#check @jacobi.Support.envelope_estimates

/-!
jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proved.
-/
#check @jacobi.Support.groundCauchyKernel_topProfile
#check @jacobi.Support.continuum_volterra_complete
#check @jacobi.Support.source_continuum_volterra
#check @jacobi.Support.groundTriangle_source
#check @jacobi.Support.groundTriangle_target
#check @jacobi.Support.groundCauchyAction_nested

/-!
jacobi, Appendix C.3 (complex edge-wave convergence).
Proved.
-/
#check @jacobi.Support.naturalWave_dimension_edge
#check @jacobi.Support.correctedEdgeEnergy_eq
#check @jacobi.Support.correctedEdgeEnergy_limit
#check @jacobi.Support.supportPolynomial_edge

/-!
jacobi, Appendix C.3 (support weights and segment bounds).
Proved.
-/
#check @jacobi.Support.weight_mesh_scale
#check @jacobi.Support.supportWeight_right_bounds
#check @jacobi.Support.supportWeight_bounds
#check @jacobi.Support.supportPolynomial_segment_bounds

/-!
jacobi, Proposition C.3. Finite waves and resolvent limit
Proved.
-/
#check @jacobi.Comparison.target_eigenvector_half_uniform
#check @jacobi.Comparison.target_eigenvector_uniform_limit
#check @jacobi.Comparison.target_eigenvector_full_limit
#check @jacobi.Comparison.topConstant_amplitude
#check @jacobi.Comparison.targetWeight_limit
#check @jacobi.Comparison.targetWeight_characteristic_limit
#check @jacobi.Comparison.target_energy_limit
#check @jacobi.Comparison.target_diagonal_floor_limit
#check @jacobi.Comparison.finiteNuclearGreen_operator
#check @jacobi.Comparison.embeddedGreenOperator_trace_limit
#check @jacobi.Comparison.embeddedGreenOperator_difference_traceClass

/-!
jacobi, Appendix C.4 (target/support weight ratios).
Proved.
-/
#check @jacobi.Comparison.relativeGapProductAt_tendsto
#check @jacobi.Comparison.comparisonNormalizer_tendsto
#check @jacobi.Comparison.comparisonWeightAt_tendsto
#check @jacobi.Comparison.comparisonNormalizer_reflection
#check @jacobi.Comparison.comparisonWeightAt_reflection
#check @jacobi.Comparison.comparisonWeightAt_reflected_tendsto

/-!
jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proved.
-/
#check @jacobi.Comparison.gramKernelError_limit
#check @jacobi.Comparison.gramPerturbation_uniform
#check @jacobi.Comparison.half_quadratic_error
#check @jacobi.Comparison.targetGram_quadratic
#check @jacobi.Comparison.targetGram_uniform_coercive

/-!
jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proved.
-/
#check @jacobi.Finite.DiscreteMeasure.evaluate_schurPolynomial
#check @jacobi.Finite.DiscreteMeasure.schurPolynomial_degree_le
#check @jacobi.Finite.DiscreteMeasure.schur_formula
#check @jacobi.Comparison.rowCoefficient_system
#check @jacobi.Comparison.rowCoefficient_perturbation_system

/-!
jacobi, Appendix C.4 (uniform Cholesky limit).
Proved.
-/
#check @jacobi.Comparison.choleskyError_equation
#check @jacobi.Comparison.cholesky_uniform_limit

/-!
jacobi, Appendix C.4 (uniform eigenvector limits).
Proved.
-/
#check @jacobi.Comparison.target_eigenvector_half_uniform
#check @jacobi.Comparison.target_eigenvector_uniform_limit
#check @jacobi.Comparison.target_eigenvector_full_limit

/-!
jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proved.
-/
#check @jacobi.Reference.zeroGreenFactor_referenceCoefficient
#check @jacobi.Reference.zeroGreen_factorization_pos
#check @jacobi.Reference.zeroGreen_factorization

/-!
jacobi, Proposition C.4. Precise endpoint behavior
Proved.
-/
#check @jacobi.Trichotomy.endpointWeight_bessel
#check @jacobi.Trichotomy.endpointConstant_bessel
#check @jacobi.Trichotomy.endpointConstant_bessel_hasSum
#check @jacobi.Trichotomy.critical_ratio_limit
#check @jacobi.Trichotomy.critical_profile_real_limit
#check @jacobi.Trichotomy.critical_profile_limit
#check @jacobi.Trichotomy.supercritical_profile_difference_limit
#check @jacobi.Trichotomy.supercritical_profile_limit
#check @jacobi.Trichotomy.subcritical_inverse_atLeft
#check @jacobi.Trichotomy.subcritical_density_tail_atLeft
#check @jacobi.Trichotomy.subcritical_density_tail
#check @jacobi.Trichotomy.critical_density_coordinate_tail
#check @jacobi.Trichotomy.critical_density_tail_atBot
#check @jacobi.Trichotomy.critical_density_tail
#check @jacobi.Trichotomy.supercritical_density_tail_atBot
#check @jacobi.Trichotomy.packedDensity_abs
#check @jacobi.Trichotomy.supercritical_density_tail
#check @jacobi.Trichotomy.packedDensity_mass
#check @jacobi.Trichotomy.packedDensity_root_mass
#check @jacobi.Trichotomy.packedDensity_energy

/-!
jacobi, Theorem C.5. Shifted resolvent limits
Proved.
-/
#check @jacobi.EdgeResolvent.finiteShiftedDiagonal_uniform
#check @jacobi.EdgeResolvent.finiteShiftedDiagonal_bound
#check @jacobi.EdgeResolvent.finiteShiftedDiagonal_floor_uniform
#check @jacobi.EdgeResolvent.finiteShifted_square_budget
#check @jacobi.EdgeResolvent.finiteShiftedSquare_energy_uniform
#check @jacobi.EdgeResolvent.finiteShiftedNormSquare_energy_uniform
#check @jacobi.EdgeResolvent.complex_matrix_inv_neg
#check @jacobi.EdgeResolvent.targetResolvent_reflection
#check @jacobi.EdgeResolvent.targetResolvent_diagonal_reflection

/-!
jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proved.
-/
#check @jacobi.EdgeResolvent.resolventTransform_sub_bound
#check @jacobi.EdgeResolvent.finiteShiftedEdge_l1_uniform
#check @jacobi.EdgeResolvent.finiteShiftedEdge_compact_bound
#check @jacobi.EdgeResolvent.real_edgePoint_above_nodes

/-!
jacobi, Corollary C.6. Shifted real two-sided bounds
Proved.
-/
#check @jacobi.EdgeResolvent.realShiftedProfile_cast
#check @jacobi.EdgeResolvent.realShiftedCandidate_energy_limit
#check @jacobi.EdgeResolvent.shiftedOptimalEnergy_upper

/-!
jacobi, Appendix D.1 (trace-class feature operators).
Proved.
-/
#check @jacobi.Continuum.composedFeature_integrable
#check @jacobi.Continuum.composedDensity_val
#check @jacobi.Continuum.composedDensity_trace

/-!
jacobi, Appendix D.1 (ground parameter).
Proved.
-/
#check @jacobi.Variational.topGradient_pairing
#check @jacobi.Variational.topGradient_formula
#check @jacobi.Variational.top_variation

/-!
jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proved.
-/
#check @jacobi.Variational.L1Source.secondPairing_self
#check @jacobi.Variational.second_expansion
#check @jacobi.Variational.second_expansion_remainder
#check @jacobi.Variational.operator_pairing_bound
#check @jacobi.Variational.gapped_rayleigh_upper
#check @jacobi.Variational.top_eigenvalue_expansion

/-!
jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proved.
-/
#check @jacobi.Variational.L1Source.fredholmDerivativeOperator_symmetric
#check @jacobi.Variational.fredholmDerivative_diagonal
#check @jacobi.Variational.fredholm_klein
#check @jacobi.Variational.fredholmResolvent_distance
#check @jacobi.Variational.fredholmDerivativeOperator_distance
#check @jacobi.Variational.fredholmGradient_distance

/-!
jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proved.
-/
#check @jacobi.Rearrangement.exists_l1_rearrangement
#check @jacobi.Rearrangement.exists_equimeasurable_rearrangement
#check @jacobi.Rearrangement.exists_radial_replacement
#check @jacobi.Rearrangement.exists_radial_moment_replacement
#check @jacobi.Variational.ground_slope_neg
#check @jacobi.Variational.ground_strictAnti
#check @jacobi.Variational.ground_symmetricDecreasing

/-!
jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proved.
-/
#check @jacobi.Variational.radial_reflected_difference
#check @jacobi.Variational.convolutionSlope_reflected
#check @jacobi.Variational.convolutionSlope_radial_neg
#check @jacobi.Variational.ground_slope_neg
#check @jacobi.Variational.ground_strictAnti
#check @jacobi.Variational.ground_symmetricDecreasing

/-!
jacobi, Appendix D.1 (radial tail bounds).
Proved.
-/
#check @jacobi.Variational.energy_tail
#check @jacobi.Variational.SymmetricDecreasing.root
#check @jacobi.Variational.root_tail

/-!
jacobi, Lemma D.1. Spectral compactness
Proved.
-/
#check @jacobi.Variational.compact_mass_subsequence
#check @jacobi.Variational.compact_subsequence
#check @jacobi.Variational.fredholm_limit_of_subcritical
#check @jacobi.Variational.fredholm_limsup
#check @jacobi.Variational.compact_subsequence_with_fredholm
#check @jacobi.Variational.root_limit_at_liminf

/-!
jacobi, Appendix D.1 (moment and Fredholm relaxations).
Proved.
-/
#check @jacobi.Variational.Density
#check @jacobi.Variational.EdgeSpectrum
#check @jacobi.Variational.EdgeSpectrum.second_lt_mass_sq
#check @jacobi.Variational.fredholm_mono_of_moments
#check @jacobi.Variational.Density.fredholm_mono
#check @jacobi.Variational.L1Source.fredholm_second_lower

/-!
jacobi, Appendix D.1 (lower semicontinuity).
Proved.
-/
#check @jacobi.Variational.mass_liminf
#check @jacobi.Variational.integrable_limit_of_bound
#check @jacobi.Variational.finite_energy_limit
#check @jacobi.Variational.spectrum_limit_of_l1
#check @jacobi.Variational.fredholmSpectrum_le_liminf
#check @jacobi.Variational.fredholm_le_liminf_of_l1

/-!
jacobi, Proposition D.2. Existence
Proved.
-/
#check @jacobi.Variational.mass_pos_of_observe_pos
#check @jacobi.Variational.moment_minimizer_exists
#check @jacobi.Variational.moment_infimum_ne_top
#check @jacobi.Variational.fredholm_feasible
#check @jacobi.Variational.mass_pos_of_fredholm_pos
#check @jacobi.Variational.fredholm_minimizer_exists

/-!
jacobi, Appendix D.1 (strict concentration gain).
Proved.
-/
#check @jacobi.Variational.laplacePair_dilate
#check @jacobi.Variational.laplacePair_second
#check @jacobi.Variational.second_strict_dilation
#check @jacobi.Variational.fredholm_strict_dilation_extended
#check @jacobi.Variational.dilation_pole_margin
#check @jacobi.Variational.fredholm_strict_dilation

/-!
jacobi, Lemma D.3. Common multiplier rule
Proved.
-/
#check @jacobi.Variational.normal_multiplier_rule_local
#check @jacobi.Variational.normal_multiplier_rule
#check @jacobi.Variational.dilation_constraint_qualification
#check @jacobi.Variational.second_constraint_qualified
#check @jacobi.Variational.top_constraint_qualified

/-!
jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proved.
-/
#check @jacobi.Variational.second_gradient_pairing
#check @jacobi.Variational.second_minimizer_kkt
#check @jacobi.Variational.second_minimizer_kkt_exists
#check @jacobi.Variational.top_minimizer_kkt
#check @jacobi.Variational.top_minimizer_kkt_exists
#check @jacobi.Variational.kkt_coefficient_shape
#check @jacobi.Variational.second_minimizer_shape
#check @jacobi.Variational.top_minimizer_shape

/-!
jacobi, Theorem D.4. Full transfer
Proved.
-/
#check @jacobi.Variational.fibreEnergyInfimum_toReal
#check @jacobi.Variational.fibre_transfer
#check @jacobi.Variational.fibre_transfer_article

/-!
jacobi, Appendix D.3 (quadrature positivity and monotonicity).
Proved.
-/
#check @jacobi.Elliptic.P_fredholm_hasDerivAt
#check @jacobi.Elliptic.inverse_sqrt_shape_hasDerivAt
#check @jacobi.Elliptic.inverse_sqrt_fredholm_hasDerivAt

/-!
jacobi, Theorem D.5. Mass-constrained second moment
Proved.
-/
#check @jacobi.Elliptic.ratio_endpoints
#check @jacobi.Elliptic.ratio_strictAntiOn_closed
#check @jacobi.Elliptic.unique_ratio_parameter
#check @jacobi.Elliptic.elliptic_optimizer_exact
#check @jacobi.Elliptic.elliptic_calibration
#check @jacobi.Elliptic.elliptic_edge_calibration
#check @jacobi.Young.youngValue_at_U
#check @jacobi.Young.second_calibration_at_U
#check @jacobi.Young.root_second_calibration_at_U

/-!
jacobi, Theorem D.6. Keller with a mass cap
Proved.
-/
#check @jacobi.Keller.massCurve_limit
#check @jacobi.Keller.massCurve_bounds
#check @jacobi.Keller.mass_parameter_exists_unique
#check @jacobi.Keller.edge_free_value
#check @jacobi.Keller.edge_constrained_value
#check @jacobi.Keller.jacobi_branch_criterion

/-!
jacobi, Appendix D.4 (green diagonal and determinant identities).
Proved.
-/
#check @jacobi.Variational.L1Source.green_log_determinant
#check @jacobi.Variational.integral_Iic_nonnegative_derivative
#check @jacobi.Variational.L1Source.green_ratio_square_integral

/-!
jacobi, Theorem D.7. Exact Fredholm value
Proved.
-/
#check @jacobi.Fredholm.admissible_candidate_realized
#check @jacobi.Fredholm.closed_form_alternatives
#check @jacobi.Fredholm.fredholm_closed_form
#check @jacobi.Fredholm.interior_mass_root
#check @jacobi.Fredholm.determinant_lt_scalar
#check @jacobi.Fredholm.candidate_strict_feasibility
#check @jacobi.Fredholm.Optimizer.sqrt_euler
#check @jacobi.Fredholm.candidate_multipliers
#check @jacobi.Fredholm.Optimizer.eq_candidate
#check @jacobi.Fredholm.Optimizer.free_density_tail
#check @jacobi.Fredholm.exponential_tail_global
#check @jacobi.Fredholm.candidate_exponential_decay

/-!
jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proved.
-/
#check @jacobi.Fredholm.conserved_hasDerivAt
#check @jacobi.Fredholm.green_first_integral
#check @jacobi.Fredholm.Optimizer.force_hasDerivAt
#check @jacobi.Fredholm.Optimizer.turning_point
#check @jacobi.Fredholm.Optimizer.shape

/-!
jacobi, Appendix D.4 (state quadratures and realized profiles).
Proved.
-/
#check @jacobi.Fredholm.Optimizer.mass_quadrature
#check @jacobi.Fredholm.Optimizer.energy_quadrature_raw
#check @jacobi.Fredholm.Optimizer.energy_quadrature
#check @jacobi.Fredholm.Optimizer.sqrt_euler
#check @jacobi.Fredholm.candidate_multipliers
#check @jacobi.Fredholm.Optimizer.eq_candidate

/-!
jacobi, Appendix D.4 (parameter derivatives and shape order).
Proved.
-/
#check @jacobi.Fredholm.log_shape_eq
#check @jacobi.Fredholm.logShape_shape_hasDerivAt_neg
#check @jacobi.Fredholm.logShape_parameter_hasDerivAt_nonneg
#check @jacobi.Fredholm.mass_parameter_continuous
#check @jacobi.Fredholm.core_shape_continuous
#check @jacobi.Fredholm.determinant_shape_continuous

/-!
jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proved.
-/
#check @jacobi.Fredholm.curve_hasDerivAt_of_partials
#check @jacobi.Fredholm.curve_envelope
#check @jacobi.Fredholm.constant_mass_envelope
#check @jacobi.Fredholm.free_determinant_deriv_pos
#check @jacobi.Fredholm.free_determinant_strictMono
#check @jacobi.Fredholm.free_root_unique
#check @jacobi.Fredholm.mass_graph_determinant_calculus
#check @jacobi.Fredholm.determinant_mass_level_order
#check @jacobi.Fredholm.interior_root_unique

/-!
jacobi, Theorem D.8. Explicit root-mass bound
Proved.
-/
#check @jacobi.RootMass.inner_exact
#check @jacobi.RootMass.root_calibration
#check @jacobi.RootMass.edge_calibration
#check @jacobi.RootMass.constraintSlopeIntegrand_pos
#check @jacobi.RootMass.Ghat_deriv_pos
#check @jacobi.RootMass.Ghat_contDiffOn

/-!
jacobi, Appendix D.5 (root-mass coordinate and inverse).
Proved.
-/
#check @jacobi.RootMass.inverse_continuous
#check @jacobi.RootMass.inverse_strictMono
#check @jacobi.RootMass.inverse_hasDerivAt

/-!
jacobi, Appendix D.5 (unrestricted inner problem).
Proved.
-/
#check @jacobi.RootMass.extendedInner_active
#check @jacobi.RootMass.extendedInner_exact
#check @jacobi.RootMass.root_calibration_L1
#check @jacobi.RootMass.narrowBox_root_integrable
#check @jacobi.RootMass.inner_feasible
#check @jacobi.RootMass.inner_minimizer_exists

/-!
jacobi, Appendix D.5 (global pointwise minimum principle).
Proved.
-/
#check @jacobi.RootMass.needle_minimum_inequality
#check @jacobi.RootMass.pointwise_minimum

/-!
jacobi, Appendix D.5 (compact root-mass profile).
Proved.
-/
#check @jacobi.RootMass.upperRoot_switch
#check @jacobi.RootMass.compactValue_ae
#check @jacobi.RootMass.compactPotential_classical
#check @jacobi.RootMass.Profile.mass
#check @jacobi.RootMass.Profile.energy
#check @jacobi.RootMass.Profile.constraint

/-!
jacobi, Appendix D.5 (regularized state quadratures).
Proved.
-/
#check @jacobi.RootMass.node_jacobian
#check @jacobi.RootMass.turningIntegral_substitution
#check @jacobi.RootMass.turningIntegral_power

/-!
jacobi, Appendix D.5 (exact positivity certificate and strict constraint monotonicity).
Proved.
-/
#check @jacobi.RootMass.S1_posDef
#check @jacobi.RootMass.certificate_identity
#check @jacobi.RootMass.PiSharp_pos
#check @jacobi.RootMass.constraintSlopeIntegrand_pos
#check @jacobi.RootMass.Ghat_deriv_pos
#check @jacobi.RootMass.Ghat_contDiffOn

/-!
jacobi, Lemma E.1. Uniform complex numbered Bessel zeros
Proved.
-/
#check @jacobi.Bessel.uniform_numbered_bessel_zeros

/-!
jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proved.
-/
#check @jacobi.Analytic.OrderDisk.normingFactor_real
#check @jacobi.Analytic.OrderDisk.normingRatio_real
#check @jacobi.Analytic.analytic_norming_products
#check @jacobi.Analytic.OrderDisk.kernelMap_continuousOn
#check @jacobi.Analytic.OrderDisk.kernelMap_holomorphic
#check @jacobi.Analytic.analytic_kernel
#check @jacobi.Analytic.OrderDisk.GL_local_complete
#check @jacobi.Analytic.analytic_GL
#check @jacobi.Analytic.analytic_GL_profile_energy
#check @jacobi.Analytic.OrderDisk.persymmetricEnergy_holomorphic
#check @jacobi.Analytic.OrderDisk.persymmetricEnergy_real
#check @jacobi.Analytic.analytic_persymmetric_energy

/-!
jacobi, Appendix E.2 (decimal table and numerical illustrations).
Excluded: decimal evaluations and numerical illustrations are outside the agreed analytic scope; no numerical premise is added to a theorem.
-/
