import chebyshev2

/-!
Article: chebyshev2 — statements in the order of the article.
Use: imported by `Check`; all references below are type-checked, and their proof bodies
are included in its module-owned axiom audit. Comments explain numerical exclusions.
The showcase introduces no additional mathematical hypotheses.
-/

/-!
chebyshev2, Theorem 1.1. Analytic Green-energy sandwich and sine limit. Omitted: The stronger
printed lower constant and the upper decimal 1.14269218 require the excluded full numerical
certificates. The proved sine interval is given in chebyshev1.
-/
#check @chebyshev2.Optimal.greenConstant_ge_one
#check @chebyshev2.Optimal.greenConstant_le_sine
#check @chebyshev2.Optimal.gainConstant_lower
#check @chebyshev2.Optimal.gainConstant_le_sine
#check @chebyshev2.Optimal.symmetricGainConstant_bounds
#check @chebyshev2.DualCertificate.uniform_sine_of_finite_lower
#check @chebyshev2.SineJacobi.gain_exact
#check @chebyshev2.SineJacobi.normalized_gain_limit
#check @chebyshev2.SineJacobi.diagonal_l2_limit
#check @chebyshev2.SineJacobi.energy_limit
#check @chebyshev2.SineJacobi.phi_formula
#check @chebyshev2.SineJacobi.energy_eq_integral

/-!
chebyshev2, Theorem 1.2. Analytic gain reduction and uniform sine comparison. Omitted: The printed
factor 1.000004 is excluded. The unconditional factor 1.000013 is checked separately at Section 4.1.
-/
#check @chebyshev2.Optimal.greenConstant_ge_one
#check @chebyshev2.Optimal.greenConstant_le_sine
#check @chebyshev2.Optimal.gainConstant_lower
#check @chebyshev2.Optimal.gainConstant_le_sine
#check @chebyshev2.Optimal.symmetricGainConstant_bounds
#check @chebyshev2.DualCertificate.uniform_sine_of_finite_lower

/-!
chebyshev2, Definition 1. Terminal-exact recurrences, gain and finite realization classes.
-/
#check @chebyshev2.Recurrence
#check @chebyshev2.Jacobi
#check @chebyshev2.Fiber

#check @chebyshev2.recurrenceEquiv
#check @chebyshev2.Jacobi.admissible
#check @chebyshev2.Jacobi.recurrence
#check @chebyshev2.Jacobi.residual_eq
#check @chebyshev2.Jacobi.recurrence_irreducible_iff
#check @chebyshev2.Jacobi.recurrence_centered_iff
#check @chebyshev2.SineJacobi.six_classes_nonempty

/-!
chebyshev2, Theorem 2.1. Bijection with all admissible Jacobi matrices, including reducible
matrices.
-/
#check @chebyshev2.recurrenceEquiv
#check @chebyshev2.Jacobi.admissible
#check @chebyshev2.Jacobi.recurrence
#check @chebyshev2.Jacobi.residual_eq
#check @chebyshev2.Jacobi.recurrence_irreducible_iff
#check @chebyshev2.Jacobi.recurrence_centered_iff
#check @chebyshev2.SineJacobi.six_classes_nonempty

/-!
chebyshev2, Theorem 2.2. Sharp gain formula, derivative and attaining examples.
-/
#check @chebyshev2.Jacobi.gain_formula
#check @chebyshev2.Jacobi.gain_lower_bound
#check @chebyshev2.Jacobi.gain_attained_dim_two
#check @chebyshev2.Jacobi.gain_bound
#check @chebyshev2.Jacobi.gain_minimal
#check @chebyshev2.Jacobi.derivative_formula

/-!
chebyshev2, Corollary 1. Symmetric gain sandwich and the sine equality case.
-/
#check @chebyshev2.Jacobi.symmetric_gain_bounds
#check @chebyshev2.SineJacobi.symmetric_gain_exact
#check @chebyshev2.Optimal.symmetricGainConstant_bounds

/-!
chebyshev2, Proposition 1. Exponential Green representation.
-/
#check @chebyshev2.Jacobi.cholesky_factor
#check @chebyshev2.Jacobi.cholesky_unique
#check @chebyshev2.Jacobi.green_exponential

/-!
chebyshev2, Theorem 2.3. Block packing, exact masses/energy and spectral distance.
-/
#check @chebyshev2.Packing.exists_representation
#check @chebyshev2.Packing.packedDensity_normalized
#check @chebyshev2.Packing.packedDensity_energy
#check @chebyshev2.Packing.packed_spectral_distance

/-!
chebyshev2, Theorem 2.4. Uniform l1 spectral transfer, ground parameter and Fredholm/cosh
observations.
-/
#check @chebyshev2.Continuum.finite_reference_distance_bound
#check @chebyshev2.Continuum.eigenvalue_l1_le_nuclearNorm
#check @chebyshev2.Continuum.reference_logDeterminant
#check @chebyshev2.Continuum.kernelEigenvalue_square_integral
#check @chebyshev2.Packing.packed_reference_distance
#check @chebyshev2.Packing.packed_ground_parameter_distance
#check @chebyshev2.Continuum.reference_fredholmDeterminant
#check @chebyshev2.Packing.packed_fredholm_observation_distance
#check @chebyshev2.Packing.packedKernel_hasSum_square_trace
#check @chebyshev2.Packing.packed_square_integral_distance

/-!
chebyshev2, Theorem 2.5. Finite sine chain and limiting elliptic profile and energy.
-/
#check @chebyshev2.SineJacobi.gain_exact
#check @chebyshev2.SineJacobi.normalized_gain_limit
#check @chebyshev2.SineJacobi.diagonal_l2_limit
#check @chebyshev2.SineJacobi.energy_limit
#check @chebyshev2.SineJacobi.phi_formula
#check @chebyshev2.SineJacobi.energy_eq_integral

/-!
chebyshev2, Definition 2. Actual sine coordinate and density.
-/
#check @chebyshev2.SineContinuum.n

/-!
chebyshev2, Proposition 2. Sine coordinate bijection, symmetry, masses, spectrum, theta formula
and tails.
-/
#check @chebyshev2.SineContinuum.sine_kernel_eigenvalue
#check @chebyshev2.SineContinuum.sine_density_eigenvalue
#check @chebyshev2.SineContinuum.n_theta
#check @chebyshev2.SineContinuum.energy
#check @chebyshev2.SineContinuum.mass
#check @chebyshev2.SineContinuum.n_theta_envelope
#check @chebyshev2.SineContinuum.sqrt_mass
#check @chebyshev2.SineContinuum.thetaDensity_log_bounds

/-!
chebyshev2, Definition 3. Spectral observations and the relaxed class.
-/
#check @chebyshev2.Continuum.kernelEigenvalue
#check @chebyshev2.Continuum.logDeterminant
#check @chebyshev2.Filters.CompactDensity.observations
#check @chebyshev2.Filters.CompactDensity.target
#check @chebyshev2.Filters.CompactDensity.relaxed
#check @chebyshev2.Filters.CompactDensity.relaxed_iff

/-!
chebyshev2, Theorem 3.1. Sharp ground-state variational principle, ODE, simplicity and intrinsic
coordinate.
-/
#check @chebyshev2.GroundState.groundParameter_variational
#check @chebyshev2.GroundState.ground_state
#check @chebyshev2.GroundState.kernel_ground_simple
#check @chebyshev2.GroundState.GroundWitness.square_identity
#check @chebyshev2.GroundState.GroundWitness.square_eq_zero_iff
#check @chebyshev2.GroundState.GroundWitness.ode
#check @chebyshev2.GroundState.GroundWitness.unique_solution
#check @chebyshev2.GroundState.GroundWitness.coordinate_limits
#check @chebyshev2.GroundState.RiccatiData.q_lipschitz
#check @chebyshev2.GroundState.RiccatiData.q_antitone_left
#check @chebyshev2.GroundState.RiccatiData.q_antitone_right

/-!
chebyshev2, Proposition 3. Actual linear/Riccati filters, causal formulas, uniqueness and spectral
observations.
-/
#check @chebyshev2.Filters.nonlinear_unique
#check @chebyshev2.Filters.nonlinear_mass_eq_logDeterminant
#check @chebyshev2.Filters.nonlinear_square_mass
#check @chebyshev2.Filters.nonlinear_causal
#check @chebyshev2.Filters.nonlinear_linearization

/-!
chebyshev2, Definition 4. Calibration data and actual cubic amplitude.
-/
#check @chebyshev2.Calibration.Data

#check @chebyshev2.Calibration.Data.base_identity
#check @chebyshev2.Calibration.Data.energy_ge_base
#check @chebyshev2.Calibration.Data.Gamma_attained
#check @chebyshev2.Calibration.Data.amplitude_spec

/-!
chebyshev2, Proposition 4. Attained contact minimum and exact nonnegative-defect base identity.
-/
#check @chebyshev2.Calibration.Data.base_identity
#check @chebyshev2.Calibration.Data.energy_ge_base
#check @chebyshev2.Calibration.Data.Gamma_attained
#check @chebyshev2.Calibration.Data.amplitude_spec

/-!
chebyshev2, Theorem 3.2. Constructed contact potential and calibrated reference.
-/
#check @chebyshev2.Calibration.ReferenceData.contact_strictMono
#check @chebyshev2.Calibration.ReferenceData.contact_image
#check @chebyshev2.Calibration.ReferenceData.contactIso
#check @chebyshev2.Calibration.ReferenceData.calibration
#check @chebyshev2.Calibration.ReferenceData.calibration_Gamma
#check @chebyshev2.Calibration.ReferenceData.calibration_constant_normalized

/-!
chebyshev2, Proposition 5. Self-consistent reference and all equality cases.
-/
#check @chebyshev2.Calibration.ReferenceData.selfConsistent_attainment
#check @chebyshev2.Calibration.ReferenceData.selfConsistent_minimum
#check @chebyshev2.Calibration.ReferenceData.selfConsistent_translation

/-!
chebyshev2, Proposition 6. One-determinant continuum and uniform finite-fiber lower bounds.
-/
#check @chebyshev2.Calibration.Data.one_determinant_lower_bound
#check @chebyshev2.Calibration.Data.packed_energy_ge_base
#check @chebyshev2.Calibration.Data.greenConstant_ge_referenceBase

/-!
chebyshev2, Theorem 3.3. A common compact probability measure for all scales.
-/
#check @chebyshev2.HalfLine.commonMeasure_ode_probability
#check @chebyshev2.HalfLine.commonMeasure_filter
#check @chebyshev2.HalfLine.commonMeasure_linear_filter
#check @chebyshev2.HalfLine.commonMeasure_defect
#check @chebyshev2.HalfLine.zero_filters
#check @chebyshev2.HalfLine.groundProfile_boundary
#check @chebyshev2.HalfLine.groundProfile_left_limit
#check @chebyshev2.HalfLine.jostProfile_boundary
#check @chebyshev2.HalfLine.jostProfile_left_limit
#check @chebyshev2.HalfLine.greenSolution_energy

/-!
chebyshev2, Definition 5. Ground/filter state and actual state dynamics.
-/
#check @chebyshev2.Residual.State


/-!
chebyshev2, Proposition 7. Exact compact state region, parametrization and attained boundaries.
-/
#check @chebyshev2.StateRegion.Scales.normalized_compact
#check @chebyshev2.StateRegion.Scales.states_iff
#check @chebyshev2.HalfLine.state_mem
#check @chebyshev2.StateRegion.Scales.lower_boundary_measure
#check @chebyshev2.StateRegion.Scales.upper_boundary_measure

/-!
chebyshev2, Definition 6. Actual comparison density with prescribed ground parameter.
-/
#check @chebyshev2.Comparison.Profile.signed_determinant_comparison
#check @chebyshev2.Comparison.Profile.signed_trace_comparison
#check @chebyshev2.Primal.comparison_density

/-!
chebyshev2, Theorem 3.4. Signed determinant and square-trace comparisons.
-/
#check @chebyshev2.Comparison.Profile.signed_determinant_comparison
#check @chebyshev2.Comparison.Profile.signed_trace_comparison
#check @chebyshev2.Primal.comparison_density

/-!
chebyshev2, Proposition 8. Integration of the residual and the spectral lower bound.
-/
#check @chebyshev2.Residual.pointwise_criterion
#check @chebyshev2.Residual.statePotential_null
#check @chebyshev2.Residual.regular_price_rhs
#check @chebyshev2.Calibration.Data.energy_ge_spectral_bound

/-!
chebyshev2, Theorem 3.5. Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
#check @chebyshev2.Residual.pointwise_criterion
#check @chebyshev2.Residual.statePotential_null
#check @chebyshev2.Residual.regular_price_rhs
#check @chebyshev2.Calibration.Data.energy_ge_spectral_bound

/-!
chebyshev2, Definition 7. General rational dual-certificate data.
-/
#check @chebyshev2.DualCertificate.Data
#check @chebyshev2.DualCertificate.RationalReference
#check @chebyshev2.DualCertificate.PolynomialPotential
#check @chebyshev2.DualCertificate.Cells
#check @chebyshev2.DualCertificate.Data.calibration

/-!
chebyshev2, Definition 8. Literal strict admissibility and the value of a certificate.
-/
#check @chebyshev2.DualCertificate.Data.Admissible
#check @chebyshev2.DualCertificate.AnalyticData.value
#check @chebyshev2.DualCertificate.AnalyticData.targetValue

/-!
chebyshev2, Theorem 3.6. Admissible certificates imply continuum, finite-fiber and gain bounds.
-/
#check @chebyshev2.DualCertificate.Data.admissible_analytic
#check @chebyshev2.DualCertificate.Data.relaxed_energy_ge_value
#check @chebyshev2.DualCertificate.Data.uniform_finite_lower_bound
#check @chebyshev2.DualCertificate.Data.greenConstant_ge_value
#check @chebyshev2.DualCertificate.Data.gainConstant_ge_value

/-!
chebyshev2, Section 4.1. Unconditional one-determinant guarantee 1.000013.
-/
#check @chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory
#check @chebyshev2.Certificates.Compact.ContactValues.contact_integral_enclosed
#check @chebyshev2.Certificates.Compact.ReferenceConstant.constant_enclosed
#check @chebyshev2.Certificates.Compact.AmplitudeValues.amplitude_integral_enclosed
#check @chebyshev2.Certificates.Compact.ReferenceBase.reference_base_enclosed
#check @chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement

/-!
chebyshev2, Proposition 9. Concrete full-dual acceptance and Table 2 values. Omitted: The
full-dual leaf inequalities and their additional integral certificates are excluded by the chosen
numerical scope.
-/

/-!
chebyshev2, Corollary 2. Printed full-dual constant and 1.000004 conclusion. Omitted: Depends on
the excluded concrete Proposition 9. Proposition 6 is instantiated independently for 1.000013.
-/

/-!
chebyshev2, Proposition 10. Exact sine-energy integral, finite sums and truncation/convergence
bounds. Omitted: The extra printed decimal precision is excluded; the sufficient kernel-proved sine
interval is reused from chebyshev1.
-/
#check @chebyshev2.SineJacobi.chain_green_diagonal_bound
#check @chebyshev2.SineContinuum.energy_eq_thetaEnergy
#check @chebyshev2.SineContinuum.energyFiniteSum_integral
#check @chebyshev2.SineContinuum.energyFiniteSum_error
#check @chebyshev2.SineContinuum.energyFiniteSum_tendsto

/-!
chebyshev2, Theorem 5.1. General measurable speed gives a density with the prescribed ground
parameter.
-/
#check @chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae
#check @chebyshev2.PrescribedSpeed.SpeedData.integral_q
#check @chebyshev2.PrescribedSpeed.SpeedData.density_integrable
#check @chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density
#check @chebyshev2.Primal.ground_exact
#check @chebyshev2.Primal.density_moment_cubic
#check @chebyshev2.Primal.determinant_cubic
#check @chebyshev2.Primal.square_trace_cubic

/-!
chebyshev2, Definition 9. Actual primal family and its finite observation constraints.
-/
namespace chebyshev2.Article
open scoped BigOperators

/--
Definition 9's exact rational data; no numerical acceptance is asserted.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Definition 9.
-/
structure PrimalCertificate where
  /-- The 17 rational Chebyshev coefficients of the central logarithmic speed profile. -/
  coefficients : Fin 17 → ℚ
  /-- Rational six-by-six approximate inverse of the constraint Jacobian, used as a chord-Newton preconditioner in Definition 9. -/
  C : Matrix (Fin 6) (Fin 6) ℚ
  /-- Rational radius of the parameter cube for the contraction argument. -/
  radius : ℚ
  /-- The parameter cube has a strictly positive radius. -/
  radius_pos : 0<radius

/--
Defines `PrimalCertificate.profile` of type `ℝ → ℝ` by `chebyshev2.Primal.profile (fun j =>
(P.coefficients j:ℝ)) ![0,1,2,3,6,7] a`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Definition 9.
-/
noncomputable def PrimalCertificate.profile (P : PrimalCertificate) (a : Fin 6 → ℝ) : ℝ → ℝ :=
  chebyshev2.Primal.profile (fun j => (P.coefficients j:ℝ)) ![0,1,2,3,6,7] a

/-
The printed polynomial profile, as an instance of the proved general family.

The precise assertion is `P.profile a t= (∑ j : Fin 17,(P.coefficients j:ℝ)*
(Polynomial.Chebyshev.T ℝ (j.val:ℤ)).eval (2*t-1))+ ∑ i : Fin 6,a i*(Polynomial.Chebyshev.T ℝ
((![0,1,2,3,6,7] i:ℕ):ℤ)).eval (2*t-1)`.

Use: this is a reusable supporting API in the module's article chain. Its exact hypotheses are
required by callers; it asserts no additional numerical certificate.

Article: chebyshev2, statements in the order of the article.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
example (P : PrimalCertificate) (a : Fin 6 → ℝ) (t : ℝ) :
    P.profile a t=
      (∑ j : Fin 17,(P.coefficients j:ℝ)*
        (Polynomial.Chebyshev.T ℝ (j.val:ℤ)).eval (2*t-1))+
      ∑ i : Fin 6,a i*(Polynomial.Chebyshev.T ℝ ((![0,1,2,3,6,7] i:ℕ):ℤ)).eval (2*t-1) :=
  chebyshev2.Primal.profile_formula _ _ _ _

end chebyshev2.Article

#check @chebyshev2.Article.PrimalCertificate
#check @chebyshev2.Article.PrimalCertificate.profile
#check @chebyshev2.Primal.chebyshevDirection
#check @chebyshev2.Primal.centralPolynomial
#check @chebyshev2.Primal.familyPolynomial
#check @chebyshev2.Primal.familySpeed
#check @chebyshev2.Primal.familyConstraintMap

#check @chebyshev2.Primal.profile_formula
#check @chebyshev2.Primal.family_ground_exact
#check @chebyshev2.Primal.profile_difference_bound
#check @chebyshev2.Primal.familyConstraintMap_c1
#check @chebyshev2.Primal.exact_primal_family_of_contraction

/-!
chebyshev2, Theorem 5.2. Contraction implies exact feasible density, uniqueness, iteration error
and energy bound.
-/
#check @chebyshev2.Primal.family_energy_ceiling

#check @chebyshev2.Primal.profile_formula
#check @chebyshev2.Primal.family_ground_exact
#check @chebyshev2.Primal.profile_difference_bound
#check @chebyshev2.Primal.familyConstraintMap_c1
#check @chebyshev2.Primal.exact_primal_family_of_contraction

/-!
chebyshev2, Proposition 11. Concrete primal residual, Jacobian and energy enclosures. Omitted: The
concrete primal numerical instance is excluded; the general exact-feasibility theorem is retained.
-/

/-!
chebyshev2, Corollary 3. Concrete feasible density strictly below sine energy. Omitted: Depends on
the excluded numerical Proposition 11.
-/

/-!
chebyshev2, Theorem 6.1. No locally sharp C1 bound from finitely many spectral observations.
-/
#check @chebyshev2.LocalObstruction.theorem_6_1
#check @chebyshev2.LocalObstruction.observationH_finite_joint_analytic
#check @chebyshev2.LocalObstruction.observationS_finite_joint_c1
#check @chebyshev2.LocalObstruction.groundObservationWitness
#check @chebyshev2.LocalObstruction.sine_green_scale_tail
#check @chebyshev2.LocalObstruction.sine_ground_square_tail

/-!
chebyshev2, Hypothesis 1. Optimality of the sine–Jacobi method. Omitted: A conjecture, not an
established theorem; deliberately outside the formal proof scope.
-/

/-!
chebyshev2, Lemma 1. Exact Green trace, square trace and fiber spectrum.
-/
#check @chebyshev2.Jacobi.green_spectrum
#check @chebyshev2.Jacobi.green_trace
#check @chebyshev2.Jacobi.green_trace_square

/-!
chebyshev2, Lemma 2. Actual derivative of the terminal residual.
-/
#check @chebyshev2.Jacobi.gain_formula
#check @chebyshev2.Jacobi.gain_lower_bound
#check @chebyshev2.Jacobi.gain_attained_dim_two
#check @chebyshev2.Jacobi.gain_bound
#check @chebyshev2.Jacobi.gain_minimal
#check @chebyshev2.Jacobi.derivative_formula

/-!
chebyshev2, Lemma 3. Unique Green factorization.
-/
#check @chebyshev2.Jacobi.cholesky_factor
#check @chebyshev2.Jacobi.cholesky_unique

/-!
chebyshev2, Theorem A.1. Centering lift, contractivity, odd Green entries and characteristic
polynomial.
-/
#check @chebyshev2.Jacobi.green_trace
#check @chebyshev2.Jacobi.green_trace_square
#check @chebyshev2.Jacobi.green_spectrum
#check @chebyshev2.Jacobi.cholesky_factor
#check @chebyshev2.Jacobi.cholesky_unique
#check @chebyshev2.Jacobi.lift_grouped_matrix
#check @chebyshev2.Jacobi.lift_centered
#check @chebyshev2.Jacobi.lift_contractive
#check @chebyshev2.Jacobi.lift_green_odd
#check @chebyshev2.Jacobi.lift_charpoly
#check @chebyshev2.centeringEquiv

/-!
chebyshev2, Lemma 4. Sobolev Hilbert space, feature operators, spectra, trace class and measure
transport.
-/
#check @chebyshev2.Sobolev.h1_separable
#check @chebyshev2.Sobolev.h1_complete
#check @chebyshev2.Sobolev.sobolevDensityOperator_form
#check @chebyshev2.Continuum.kernelOperator_positive
#check @chebyshev2.Continuum.kernelOperator_isCompact
#check @chebyshev2.Continuum.kernelOperator_isTraceClass
#check @chebyshev2.Continuum.measureOperator_transport_extended
#check @chebyshev2.Continuum.measureOperator_trace
#check @chebyshev2.Continuum.TraceClassOperator.trace_rankOne

/-!
chebyshev2, Lemma 5. Legendre operator, nonlogarithmic realization and continuum sine spectrum.
-/
#check @chebyshev2.SineContinuum.sine_kernel_eigenvalue
#check @chebyshev2.SineContinuum.sine_density_eigenvalue
#check @chebyshev2.SineContinuum.n_theta
#check @chebyshev2.SineContinuum.legendreV_domain
#check @chebyshev2.SineContinuum.legendreV_operator
#check @chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint
#check @chebyshev2.SineContinuum.sineOperator_domain_eq_range
#check @chebyshev2.SineContinuum.green_mercer_uniform
#check @chebyshev2.SineContinuum.green_mercer_diagonal_uniform

/-!
chebyshev2, Lemma 6. Uniform finite sine diagonal bound.
-/
#check @chebyshev2.SineJacobi.chain_green_diagonal_bound

/-!
chebyshev2, Lemma 7. All-order sine-energy finite-sum error and convergence.
-/
#check @chebyshev2.SineJacobi.chain_green_diagonal_bound
#check @chebyshev2.SineContinuum.energy_eq_thetaEnergy
#check @chebyshev2.SineContinuum.energyFiniteSum_integral
#check @chebyshev2.SineContinuum.energyFiniteSum_error
#check @chebyshev2.SineContinuum.energyFiniteSum_tendsto
#check @chebyshev2.SineContinuum.energy3_finite_integral

/-!
chebyshev2, Proposition 12. Exact range of three filters and boundary measures.
-/
#check @chebyshev2.StateRegion.Scales.normalized_compact
#check @chebyshev2.StateRegion.Scales.states_iff
#check @chebyshev2.HalfLine.state_mem
#check @chebyshev2.StateRegion.Scales.lower_boundary_measure
#check @chebyshev2.StateRegion.Scales.upper_boundary_measure

/-!
chebyshev2, Lemma 8. Parametrization and compactness of the state region.
-/
#check @chebyshev2.StateRegion.Scales.normalized_compact
#check @chebyshev2.StateRegion.Scales.states_iff
#check @chebyshev2.HalfLine.state_mem
#check @chebyshev2.StateRegion.Scales.lower_boundary_measure
#check @chebyshev2.StateRegion.Scales.upper_boundary_measure
#check @chebyshev2.StateRegion.Scales.article_interior_bounds
#check @chebyshev2.StateRegion.Scales.mean_zero_boundary
#check @chebyshev2.StateRegion.Scales.mean_one_boundary

/-!
chebyshev2, Lemma 9. Contact integral and exact exterior logarithmic term.
-/
#check @chebyshev2.Calibration.ReferenceData.contact_strictMono
#check @chebyshev2.Calibration.ReferenceData.contact_image
#check @chebyshev2.Calibration.ReferenceData.contactIso
#check @chebyshev2.Calibration.ReferenceData.calibration
#check @chebyshev2.Calibration.ReferenceData.calibration_Gamma
#check @chebyshev2.Calibration.ReferenceData.calibration_constant_normalized

/-!
chebyshev2, Lemma 10. Comparison-density support, boundedness, ground parameter and L1 continuity.
-/
#check @chebyshev2.Calibration.Data.comparisonDensity_continuous
#check @chebyshev2.Calibration.Data.comparisonDensity_bounded
#check @chebyshev2.Calibration.Data.reciprocalSpeed_L1_tendsto
#check @chebyshev2.Calibration.Data.massRatio_L1_tendsto
#check @chebyshev2.Comparison.Profile.density_properties

/-!
chebyshev2, Definition 10. General comparison profiles and their actual densities.
-/
#check @chebyshev2.Comparison.Profile.signed_determinant_comparison
#check @chebyshev2.Comparison.Profile.signed_trace_comparison
#check @chebyshev2.Primal.comparison_density

/-!
chebyshev2, Lemma 11. Right-filter bounds, endpoint conditions, ODE, Jost and integral formulas.
-/
#check @chebyshev2.Comparison.Profile.rightFilter_bounds
#check @chebyshev2.Comparison.Profile.rightFilter_derivative
#check @chebyshev2.Comparison.Profile.rightLinear_integral
#check @chebyshev2.Comparison.Profile.rightJost_ode
#check @chebyshev2.Calibration.Data.leftFilter_joint_continuous
#check @chebyshev2.Calibration.Data.leftLinear_joint_continuous
#check @chebyshev2.Calibration.Data.rightJost_left_expansion
#check @chebyshev2.Calibration.Data.rightLinear_reflection

/-!
chebyshev2, Lemma 12. General comparison-profile signed spectral identities.
-/
#check @chebyshev2.Comparison.Profile.signed_determinant_comparison
#check @chebyshev2.Comparison.Profile.signed_trace_comparison
#check @chebyshev2.Primal.comparison_density

/-!
chebyshev2, Lemma 13. Joint filter continuity and seventh-order endpoint defects.
-/
#check @chebyshev2.Comparison.Profile.rightFilter_bounds
#check @chebyshev2.Comparison.Profile.rightFilter_derivative
#check @chebyshev2.Comparison.Profile.rightLinear_integral
#check @chebyshev2.Comparison.Profile.rightJost_ode
#check @chebyshev2.Calibration.Data.leftFilter_joint_continuous
#check @chebyshev2.Calibration.Data.leftLinear_joint_continuous

/-!
chebyshev2, Lemma 14. Symmetric spectral observations with exact support/boundary terms.
-/
#check @chebyshev2.Comparison.symmetric_logDeterminant_support_at
#check @chebyshev2.Comparison.symmetric_square_trace_support_at

/-!
chebyshev2, Lemma 15. Attained cubic conjugate, scaling, polynomial branch and convexity.
-/
#check @chebyshev2.Residual.conjugate_isGreatest
#check @chebyshev2.Residual.conjugate_le_iff
#check @chebyshev2.Residual.conjugate_scale
#check @chebyshev2.Residual.psi_polynomial
#check @chebyshev2.Residual.psi_convex

/-!
chebyshev2, Theorem E.1. Stability of strict admissibility and uniform transfer of the certificate
value.
-/
#check @chebyshev2.DualCertificate.Data.admissible_stable
#check @chebyshev2.DualCertificate.Data.packed_value_tendsto
#check @chebyshev2.DualCertificate.Data.packed_value_uniform

/-!
chebyshev2, Lemma 16. Actual normalized coefficients, smooth endpoint quotients, state faces and
centering.
-/
#check @chebyshev2.DualCertificate.NormalizedCalibration.defect_order_seven
#check @chebyshev2.DualCertificate.NormalizedCalibration.linearDefect_order_seven
#check @chebyshev2.DualCertificate.NormalizedCalibration.actual_normalized_criterion
#check @chebyshev2.DualCertificate.NormalizedCalibration.actual_face_reduction
#check @chebyshev2.DualCertificate.NormalizedCalibration.determinantTerm_identity
#check @chebyshev2.DualCertificate.NormalizedCalibration.traceTerm_identity
#check @chebyshev2.DualCertificate.PolynomialPotential.centered_c1
#check @chebyshev2.DualCertificate.PolynomialPotential.centered_boundary
#check @chebyshev2.DualCertificate.monomial_coefficient_divisibility
#check @chebyshev2.DualCertificate.moment_coefficient_divisibility
#check @chebyshev2.DualCertificate.NormalizedCalibration.R_smooth
#check @chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth
#check @chebyshev2.DualCertificate.Data.price_cost_integrands

/-!
chebyshev2, Lemma 17. Determinant and trace cancellation identities.
-/
#check @chebyshev2.DualCertificate.NormalizedCalibration.determinantTerm_identity
#check @chebyshev2.DualCertificate.NormalizedCalibration.traceTerm_identity

/-!
chebyshev2, Lemma 18. Finite-order normalized derivative recurrences.
-/
#check @chebyshev2.Numerics.normalizedWithin_exp
#check @chebyshev2.Numerics.normalizedWithin_inverse
#check @chebyshev2.Numerics.normalizedWithin_mul
#check @chebyshev2.Numerics.normalizedWithin_riccati
#check @chebyshev2.Numerics.normalizedWithin_shifted_riccati
#check @chebyshev2.Numerics.normalizedWithin_sqrt

/-!
chebyshev2, Lemma 19. Positive cubic root, Newton enclosure and error.
-/
#check @chebyshev2.Numerics.positiveCubic_bounds
#check @chebyshev2.Numerics.positiveCubic_bracket
#check @chebyshev2.Numerics.positiveCubic_jet_recurrence
#check @chebyshev2.Numerics.positiveCubic_mono
#check @chebyshev2.Numerics.positiveCubic_newton
#check @chebyshev2.Numerics.positiveCubic_slope
#check @chebyshev2.Numerics.positiveCubic_smooth
#check @chebyshev2.Numerics.positiveCubic_spec
#check @chebyshev2.Numerics.positiveCubic_strict_mono
#check @chebyshev2.Numerics.positiveCubic_unique
#check @chebyshev2.Calibration.positive_cubic_root_unique
#check @chebyshev2.Numerics.cubicNewton_sound

/-!
chebyshev2, Lemma 20. Exact centered quadrature with the full finite-order remainder.
-/
#check @chebyshev2.Numerics.quadrature_taylor
#check @chebyshev2.Numerics.quadrature_taylor_even

/-!
chebyshev2, Lemma 21. Validated signed-slope flow: existence, uniqueness and Taylor propagation.
-/
#check @chebyshev2.Numerics.riccati_taylor_propagation
#check @chebyshev2.Numerics.riccati_unique
#check @chebyshev2.Numerics.validated_flow_step

/-!
chebyshev2, Lemma 22. Removal of a cubic zero at the available finite differentiability order.
-/
#check @chebyshev2.Calculus.removing_cubic_zero

/-!
chebyshev2, Lemma 23. Canonical polynomial translation and binomial coefficients.
-/
#check @chebyshev2.Numerics.translatePolynomial_binomial
#check @chebyshev2.Numerics.translatePolynomial_coeff
#check @chebyshev2.Numerics.translatePolynomial_eval

/-!
chebyshev2, Lemma 24. Actual multivariable segment, state and time Taylor/concavity upper bounds.
-/
#check @chebyshev2.Numerics.StateJetOn.segment_first_order_upper
#check @chebyshev2.Numerics.StateJetOn.segment_taylor_upper
#check @chebyshev2.Numerics.StateJetOn.state_concavity_upper
#check @chebyshev2.Numerics.StateJetOn.state_gradient_upper
#check @chebyshev2.Numerics.StateJetOn.state_taylor_upper
#check @chebyshev2.Numerics.StateJetOn.time_taylor_upper

/-!
chebyshev2, Lemma 25. Derived invertibility, exact zero, uniqueness and geometric chord-iteration
error.
-/
#check @chebyshev2.Primal.preconditioner_bijective
#check @chebyshev2.Primal.chord_newton_matrix
#check @chebyshev2.Primal.chord_iterate_error

/-!
chebyshev2, Proposition 13. Actual mass/spectral Frechet derivatives, C1 family and energy bound.
-/
#check @chebyshev2.Primal.density_family_moment_c1
#check @chebyshev2.Primal.mass_directional_derivative
#check @chebyshev2.Primal.sqrt_mass_directional_derivative
#check @chebyshev2.Primal.affine_family_energy_bound
#check @chebyshev2.Primal.familyLogDeterminant_derivative_printed
#check @chebyshev2.Primal.familySquareTrace_derivative_printed
#check @chebyshev2.Primal.familyLogDeterminant_c1
#check @chebyshev2.Primal.familySquareTrace_c1
#check @chebyshev2.Primal.proposition_13

/-!
chebyshev2, Lemma 26. Actual observation gradients and the ground-state derivative.
-/
#check @chebyshev2.LocalObstruction.theorem_6_1
#check @chebyshev2.LocalObstruction.observationH_finite_joint_analytic
#check @chebyshev2.LocalObstruction.observationS_finite_joint_c1
#check @chebyshev2.LocalObstruction.groundObservationWitness
#check @chebyshev2.LocalObstruction.sine_green_scale_tail
#check @chebyshev2.LocalObstruction.sine_ground_square_tail
#check @chebyshev2.LocalObstruction.observation_analytic_neighborhood
#check @chebyshev2.LocalObstruction.resolventGreen_density_derivative

