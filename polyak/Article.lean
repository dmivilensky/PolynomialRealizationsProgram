import polyak
import polyak.ArticleResults.First
import polyak.ArticleResults.Middle
import polyak.ArticleResults.Last

/-!
# Two Answers on Heavy-Ball Dynamics: ordered article statements

Every numbered result appears in PDF order with its printed type, number, title and stable TeX
label. Each block checks the actual declarations giving its full content; the comments explain
the translation of measures, domains and quantifiers. All proofs are included in `polyak.Check`
and its transitive axiom audit. See `ArticleMap.md` for the same ordered correspondence and
unnumbered mathematics.
-/

/-!
Article: Theorem 2.1 [thm:rate]. Exact rate and realization.

Both actual worst-case root limits, the uniform optimal bound from a single five-dimensional
objective and start, and the explicit three-dimensional spiral lower bound.

exact_rate_all_horizon_bounds quantifies one f and x₀ before every N, so its attainment is
uniform in the horizon. CenteredSmoothStronglyConvex records the original smooth strongly convex
class with minimizer 0; centering is transported by normalization. worst and worstAll are the
original dimension-five and dimension-unrestricted suprema with initialization from rest.
-/
#check @polyak.Results.exact_rate_root_limits
#check @polyak.Results.exact_rate_all_horizon_bounds
#check @polyak.Realization.ExplicitSpiral.exists_spiral_lower
#check @polyak.Boundary.Classification.boundary_formula

/-!
Article: Theorem 2.2 [thm:threshold]. Sharp convergence threshold.

Sharp necessary and sufficient condition for convergence on every original objective;
quantitative critical three-cycle and supercritical exponential divergence.

converges_on_all_iff quantifies every finite dimension, original objective, minimizer and start.
The critical theorem gives a nonconstant period-three sequence p, norm-one cycle, error tending
to zero, and the stated 1/√5 bound. The divergent theorem uses the same explicit spiral
construction and includes both factor>1 and norm tending to infinity.
-/
#check @polyak.Threshold.converges_on_all_iff
#check @polyak.Threshold.sharp_rate_threshold
#check @polyak.Threshold.rate_le_sqrt_of_condition
#check @polyak.Results.exists_critical_three_cycle_quantitative
#check @polyak.Results.exists_exponential_divergence_quantitative

/-!
Article: Theorem 2.3 [thm:regularity]. Regularity and critical behavior.

Continuity, strict increase, analyticity away from exactly the five listed possible switches,
critical expansion, both small-q expansions and the large-condition-number quartic limit.

Results.regularity contains all analytic conclusions as one conjunction.
conditionRate_eq_originalRate identifies its scalar function with the actual rate. The separate
root-uniqueness, specification and bracket declarations supply the quartic and printed decimal.
-/
#check @polyak.Results.regularity
#check @polyak.Results.switching_points_ordered
#check @polyak.Asymptotics.conditionRate_eq_originalRate
#check @polyak.Asymptotics.existsUnique_limitingQuartic_root
#check @polyak.Asymptotics.limitingFactor_spec
#check @polyak.Asymptotics.limitingFactor_bounds

/-!
Article: Definition 2.4 [def:feasible]. Feasible spectrum.

The minimizer inequality and both signed lag inequalities for every positive integer lag.

MixtureFeasible directly gives |C|≤spectrumG and ∀n≥1 both signed lag inequalities for an
arbitrary continuous complex multiplier, including all general tunings. spectrumCoordinates is
the homeomorphism from probability measures on the angle interval[0,π] to the cosine
interval[−1,1], so the coordinate convention preserves the full weak-measure formulation.
-/
#check @polyak.Waves.MixtureFeasible
#check @polyak.Spectral.spectrumCoordinates

/-!
Article: Theorem 2.5 [thm:spectralgeneral]. Spectral characterization.

Exact strict-separation alternative, strict original-rate upper bound, and one fixed
finite-dimensional from-rest realization at every feasible atomic exponent.

Separation treats arbitrary continuous wave multipliers, hence applies to the stated stable
heavy-ball multiplier. The upper theorem already discharges the certificate-to-energy
implication. exists_startup and exp_le_originalRate require exactly positive curvature/step,
nonnegative momentum <1, quadratic stability and strict minimizer slack only for t>0; these are
exactly the standing hypotheses of the spectral characterization.
-/
#check @polyak.Duality.infeasible_iff_strictCertificate
#check @polyak.Growth.originalRate_lt_exp_of_certificates
#check @polyak.Realization.exists_startup
#check @polyak.Realization.exp_le_originalRate

/-!
Article: Theorem 2.6 [thm:spectral]. Spectral rate for Polyak's tuning.

The original rate equals exp T; V is even and bounded, its feasible twists form a closed
interval, and every noncritical optimum has finite interior support, strict minimizer slack and
finite active lag set.

spectral_rate directly packages all parts. The finite set is uniform over all feasible optimal
ν,C at the given nonzero exponent T; every such measure gives zero mass to its complement.
-/
#check @polyak.Spectral.spectral_rate

/-!
Article: Proposition 2.7 [prop:spiral]. The special spiral.

The special one-frequency spiral is feasible; the three displayed active slacks vanish; every
lag has the stated kernel formula; the polynomial relation is exact.

The feasible theorem is stronger, also allowing t=0. Natural-coefficient
kernel_polynomial_representation and strict positivity handle the polynomial assertion for every
n≥3. actual_relation_iff proves both directions of the rho=e^t quartic relation.
-/
#check @polyak.Spiral.feasible
#check @polyak.Spiral.lower_one_zero
#check @polyak.Spiral.upper_two_zero
#check @polyak.Spiral.upper_three_zero
#check @polyak.Spiral.mean_lower_eq
#check @polyak.Spiral.mean_upper_eq
#check @polyak.Spiral.actual_relation_iff
#check @polyak.Spiral.kernel_polynomial_representation
#check @polyak.Spiral.kernel_add_three_pos

/-!
Article: Theorem 2.8 [thm:classification]. Complete spectral classification.

The full piecewise algebraic boundary on all four physical regimes, matching endpoints, unique
scalar prescription, and an optimum with at most two frequencies.

boundary_formula uses the literal piecewise u of Classification.Value with P1/P5 continuations
and P2 parametrization. scalar_prescription is ∃!t, t−V(t)=log q under exactly q∈(0,1). Actual
roots and exact decimal brackets are checked in the cited root declarations. The two-atom result
constructs an optimal measure with at most two frequencies, including at the critical exponent.
-/
#check @polyak.Boundary.Classification.boundary_formula
#check @polyak.Boundary.Classification.u5_Ga
#check @polyak.Boundary.Classification.u5_one
#check @polyak.Boundary.Classification.u_continuousOn
#check @polyak.Boundary.Classification.exists_twoAtom_optimal
#check @polyak.Regularity.scalar_prescription
#check @polyak.Regularity.logarithmicCoordinate_strictMono
#check @polyak.Boundary.logarithmicCoordinate_continuous
#check @polyak.Boundary.P2.Ga_bounds
#check @polyak.Boundary.P2.GaRoot
#check @polyak.Boundary.P2.zetaA_bounds
#check @polyak.Boundary.P2.endpointCubic_zeta1
#check @polyak.Boundary.P2.N12_zetaA
#check @polyak.Boundary.Classification.SwitchSource.G1_fine_bounds
#check @polyak.Boundary.Classification.u
#check @polyak.Boundary.Classification.u2_G1
#check @polyak.Boundary.Classification.u1_GW
#check @polyak.Boundary.spiralSwitch_G1
#check @polyak.ArticleResults.classification_critical_data

/-!
Article: Definition 3.1 [def:angle]. Angle function.

The angle between the original wave factors and the polar representation of g−2is.

angle is arccos(Xi(cosω)/sqrt(Xi²+sin²ω)); angle_mem and threshold_polar prove its correct
branch and the polar identity. Tuning includes precisely the positive curvature, step and
quadratic-stability domain with 0≤β<1.
-/
#check @polyak.General.Tuning.angle
#check @polyak.General.Tuning.angle_mem
#check @polyak.General.Tuning.angle_pi
#check @polyak.General.Tuning.threshold_polar

/-!
Article: Theorem 3.2 [thm:oneexp]. One exponent suffices.

One strict certificate above the stable plant radius gives a strict upper bound for the original
rate; zero infeasibility gives rate<1.

Tuning.one_exponent derives the square-summable execution estimate and strict restart
improvement from a strict certificate. r0 is the actual characteristic root radius. The second
declaration directly uses zero infeasibility.
-/
#check @polyak.General.Tuning.one_exponent
#check @polyak.General.Tuning.infeasible_zero_rate_lt_one

/-!
Article: Theorem 3.3 [thm:A]. Phase locking.

The strict lag-one phase criterion, rational phase-locked periodic counterexamples, strict
tongues, closure rate bound and boundary of actual convergence.

The original-coordinate declarations include the nonlinear iterates and a single R³ objective.
rational phase hypotheses include coprimality, 1≤j and 2j<k exactly as in the article.
phase_locked_on_convergence_boundary places the tuning on the frontier of ConvergesAll.
-/
#check @polyak.General.Regions.omegaOne_iff_angle
#check @polyak.General.Regions.closure_omegaOne_rate_le_one
#check @polyak.General.Regions.phase_locked_rate_eq_one
#check @polyak.General.Regions.original_omegaOne_converges
#check @polyak.General.Regions.original_exists_periodic_orbit
#check @polyak.General.Regions.one_lt_rate_of_strict_phase
#check @polyak.General.Regions.phase_locked_on_convergence_boundary

/-!
Article: Theorem 3.4 [thm:B]. Rates.

The admissible radii form a nonempty interval with supremum 1; rhoQ≤rho≤r1<1; the exact endpoint
cubic test identifies the quadratic regime; underdamping gives a strict gap.

Radii uses sInf only after proving nonemptiness and a lower bound. rOne_eq_rhoQ_iff retains
sqrtβ<rhoQ. The underdamped declaration covers equality rhoQ=sqrtβ, including coincident roots.
-/
#check @polyak.General.Regions.admissibleRadii_nonempty
#check @polyak.General.Regions.admissibleRadii_ordConnected
#check @polyak.General.Regions.admissibleRadii_isLUB_one
#check @polyak.General.Regions.original_rate_bounds
#check @polyak.General.Regions.rOne_eq_rhoQ_iff
#check @polyak.General.Regions.original_rate_eq_quadratic_of_cubic
#check @polyak.General.Regions.underdamped_rate_strict

/-!
Article: Corollary 3.5 [cor:D]. Polyak's tuning and gradient descent.

The exact Polyak phase threshold and critical three-contact; every stable gradient-descent
tuning belongs to Ω1 and Q and has its exact quadratic rate.

gradientDescent_rOne_eq proves the gradient-descent Q assertion and identifies the lag-one bound
with the quadratic rate. Original μ,L,α units are retained in gradientDescent_rate_eq. Polyak
boundary and phase-contact declarations identify both topology and K=3.
-/
#check @polyak.General.Regions.polyak_mem_omegaOne_iff_condition
#check @polyak.General.Regions.polyak_three_tongue_iff_condition
#check @polyak.General.Regions.critical_polyak_on_omegaOne_boundary
#check @polyak.General.Regions.critical_polyak_three_contact
#check @polyak.General.Regions.gradientDescent_mem_omegaOne
#check @polyak.General.Regions.gradientDescent_rate_eq
#check @polyak.General.Regions.gradientDescent_rOne_eq

/-!
Article: Definition 3.6 [def:FP]. Full program and certificate symbols.

Full finite positive Borel-measure program, restricted lag programs, finite nonnegative
certificate symbols and strict symbols.

ProgramSolution explicitly requires IsFiniteMeasure, w≠0, the minimizer integral and every lag
integral. CertificateSymbol contains a finite lags set within the prescribed allowed set with
nonnegative coefficients; StrictSymbol supplies ε>0 and the uniform negative bound.
-/
#check @polyak.Levels.ProgramSolution
#check @polyak.Levels.FPOn
#check @polyak.Levels.FP
#check @polyak.Levels.CertificateSymbol
#check @polyak.Levels.CertificateSymbol.eval
#check @polyak.Levels.StrictSymbol

/-!
Article: Theorem 3.7 [thm:exactthr]. Exact threshold criterion.

Full threshold equivalence, density reweighting bijection, dependence only on Xi, uniform
all-horizon nonconvergence lower bound and the strict-symbol alternative.

thresholdSpectrumEquiv is a equivalence of the normalized source spectra and normalized
full-program solutions, constructed by positive density and reciprocal reweighting.
fp_worstAll_lower supplies one positive c uniformly over all horizons; the finite-dimensional
objective may depend on the horizon. The three criterion predicates refer to the original rate.
-/
#check @polyak.Levels.threshold_spectral_C_iff_fp
#check @polyak.Levels.thresholdSpectrumEquiv
#check @polyak.Levels.fp_iff_of_Xi_eq
#check @polyak.Levels.sourceDensity_eq_norm_g_minus_2is
#check @polyak.Levels.threshold_spectral_iff_of_coefficients_eq
#check @polyak.Levels.fp_worstAll_lower
#check @polyak.Levels.fp_one_le_rate
#check @polyak.Levels.rate_lt_one_iff_infeasible
#check @polyak.Levels.rate_lt_one_iff_strictSymbol
#check @polyak.Levels.divergenceSet_iff_fp

/-!
Article: Theorem 3.8 [thm:tangency]. The boundary of $\Omega_1$.

Every weak nonperiodic contact admits the literal two-lag strict certificate and has rate<1;
boundary feasibility occurs exactly at the rational locked contacts with rate=1.

nonperiodic_tangency_certificate quantifies K≥2, the strict window, a StrictSymbol and its exact
lags={1,−K}. The frontier equality is a literal full-program feasibility-set equality. The weak
phase condition includes ω=0, where Θ(0)=π makes it automatic.
-/
#check @polyak.Levels.Geometry.nonperiodic_tangency_certificate
#check @polyak.Levels.Geometry.phase_locked_boundary_rate_eq_one
#check @polyak.Levels.Geometry.frontier_inter_feasible_eq_phase_locked

/-!
Article: Definition 3.9 [def:levels]. Gaps.

Gap I_K: a nonempty dip confined to its open first-harmonic window with both endpoint
inequalities strict.

Gap unfolds to K≥2, nonempty dip, every dip frequency strictly inside the stated window and the
two strict endpoint phase tests.
-/
#check @polyak.Levels.Geometry.Gap

/-!
Article: Theorem 3.10 [thm:levelzero]. Level zero.

Exactly one complete level-zero alternative, including the actual grid atom, rate, frontier,
unique gap index and the point/interior split.

levelZero_exactly_one is ∃! over a three-constructor enum. LevelZeroAlternative expands every
article conclusion, including non-phase-locking for the singleton case. point_window_not_gap
excludes overlap of its two subcases.
-/
#check @polyak.Levels.Geometry.LevelZeroAlternative
#check @polyak.Levels.Geometry.levelZero_exactly_one
#check @polyak.Levels.Geometry.point_window_not_gap

/-!
Article: Theorem 3.11 [thm:sampling]. Periodic sampling.

The full threshold is the infimum of periodic thresholds; each divergent tuning has a persistent
periodic witness or eventual witnesses at every larger condition number; divergence is the
closure of periodic tongues.

The cited declarations apply the smoothing and sampling construction of actual_periodic_sampler.
The second branch has ∀κ′>κ then ∃L0 then ∀L≥L0, exactly the article quantifier order.
-/
#check @polyak.Global.Sampling.sigma_eq_iInf_sigmaPeriodic
#check @polyak.Global.Sampling.periodic_alternative
#check @polyak.Global.Sampling.divergence_eq_closure_periodicUnion

/-!
Article: Theorem 3.12 [thm:global]. Global structure.

All finite periodic thresholds and the full threshold are continuous; strict kappa decrease and
near-one blow-up; the global divergence epigraph has a continuous boundary valued in (1,+∞].

global_structure_a,b,c directly state the three parts. The target ExtendedConditionNumber is the
order-topological EReal subtype 1<x, including +∞ and continuity at the zero-momentum face β=0.
-/
#check @polyak.Global.Threshold.global_structure_a
#check @polyak.Global.Threshold.global_structure_b
#check @polyak.Global.Threshold.global_structure_c

/-!
Article: Proposition 3.13 [prop:13]. A two-harmonic thirteen-cycle.

The exact rational thirteen-cycle example lies in I4, excludes one-atom feasibility, has the
stated two harmonics and realizes a nonconvergent five-dimensional trajectory.

proposition_thirteen combines the gap conditions with all signed integer lag inequalities, using
their periodic residues. The harmonic theorem gives one original objective, an isometric
two-complex-mode inclusion, lower bound at all horizons and convergence to its period-thirteen
orbit. The source weights and rational tuning are literal definitions.
-/
#check @polyak.CertifiedExamples.Rational.proposition_thirteen
#check @polyak.CertifiedExamples.Rational.proposition_thirteen_actual_harmonics
#check @polyak.CertifiedExamples.Rational.thirteen_all_integer_lags

/-!
Article: Proposition 3.14 [prop:conv-gap]. Convergence in a gap.

The exact rational convergence example lies in I4 and satisfies the displayed two-lag inequality
with rational multipliers, hence rate<1.

proposition_convergence_gap includes the inequality uniformly on c∈[−1,1], with multipliers
13/100 and 1/1000. It concludes the original nonlinear rate bound.
-/
#check @polyak.CertifiedExamples.Rational.proposition_convergence_gap

/-!
Article: Theorem 3.15 [thm:class]. Classification.

The three exhaustive disjoint gap regimes have the stated signs, finite certificates or periodic
witnesses and rates; every feasible periodic measure has the Farey anchor and denominator
bounds.

BelowBoundaryCase, AboveBoundaryCase and OnBoundaryCase are expanded article conjunctions. The
anchor theorem is universal over the feasible measure and uses actual carried-by-grid data.
RegularData supplies the regular subcase; exhaustion and anchor localization hold for every
indicated gap tuning.
-/
#check @polyak.ModeLocking.BelowBoundaryCase
#check @polyak.ModeLocking.AboveBoundaryCase
#check @polyak.ModeLocking.OnBoundaryCase
#check @polyak.ModeLocking.gap_classification
#check @polyak.ModeLocking.gap_classification_disjoint
#check @polyak.ModeLocking.boundary_regimes_disjoint
#check @polyak.ModeLocking.gap_classification_anchor

/-!
Article: Theorem 3.16 [thm:modelock]. Mode locking.

A regular source point has an open analytic fixed-support continuation, exact full/periodic
thresholds, determinant identity, complete extremal classification, positive weighted gradient
and analytic divergence boundary.

ArticleResults.mode_locking exposes all five article conclusions in one type: a common open U,
real analytic shift and positive masses with exact base values, full/periodic threshold
equalities, determinant zero, full primal solution, every extremal with its exact admissible
zero mass, positive normalized gradient weights, negative kappa derivative and persisted
regularity with the same support and lags. RegularData gives the stated regularity hypotheses;
the theorem proves continuation existence, transversality and sign persistence. The separate
analytic_divergence_boundary gives the s*=0 consequence.
-/
#check @polyak.ArticleResults.mode_locking
#check @polyak.ModeLocking.RegularData.analytic_divergence_boundary

/-!
Article: Theorem 3.17 [thm:plateaus]. Two mixed-spectrum plateaus.

Both exact table rows yield regular analytic plateaus with their stated support, unique anchor,
admissible zero atom and exact period obstructions.

row18_regularData and row21_regularData construct regularity from exact interval bounds. The
boundary coordinate plus strict global kappa monotonicity gives the unique boundary value.
first_plateau_periods gives the literal divisibility-by18 characterization throughout the entire
first plateau. second_plateau_support proves positive mass at every one of the three nonzero
frequencies and absence of any other nonzero frequency throughout the entire second plateau,
retaining the admissible zero atom.
-/
#check @polyak.CertifiedExamples.Plateaus.row18_regularData
#check @polyak.CertifiedExamples.Plateaus.row21_regularData
#check @polyak.CertifiedExamples.Plateaus.row18_gap
#check @polyak.CertifiedExamples.Plateaus.row21_gap
#check @polyak.CertifiedExamples.Plateaus.row18_boundary_coordinate
#check @polyak.CertifiedExamples.Plateaus.row21_boundary_coordinate
#check @polyak.CertifiedExamples.Plateaus.row18_open_plateau
#check @polyak.CertifiedExamples.Plateaus.row21_open_plateau
#check @polyak.CertifiedExamples.Plateaus.row18_analytic_plateau
#check @polyak.CertifiedExamples.Plateaus.row21_analytic_plateau
#check @polyak.CertifiedExamples.Plateaus.row18_extremals
#check @polyak.CertifiedExamples.Plateaus.row21_extremals
#check @polyak.CertifiedExamples.Plateaus.row18_unique_anchor
#check @polyak.CertifiedExamples.Plateaus.row21_unique_anchor
#check @polyak.CertifiedExamples.Plateaus.row18_minimal_period
#check @polyak.CertifiedExamples.Plateaus.row18_no_fan_period
#check @polyak.CertifiedExamples.Plateaus.row21_no_two_atom_optimizer
#check @polyak.CertifiedExamples.Plateaus.tuning18
#check @polyak.CertifiedExamples.Plateaus.tuning21
#check @polyak.CertifiedExamples.Plateaus.tuning18_kappa_mem
#check @polyak.CertifiedExamples.Plateaus.tuning21_kappa_mem
#check @polyak.ModeLocking.Plateaus.plateau_labels
#check @polyak.ModeLocking.RegularData.extremal_iff
#check @polyak.ArticleResults.first_plateau_periods
#check @polyak.ArticleResults.second_plateau_support

/-!
Article: Definition 3.18 [def:edgesymbol]. Edge symbol.

The two adjacent lags in the inverse residue class and the signed edge symbol F=−T/2.

AdjacentData records the primitive rational frequency, inverse, adjacent lower lag and
slope=(lower+mix*k) with 0<mix<1. Its function unfolds to precisely the article combination. The
sourceFamily/intervalAdjacent constructor discharges this representation from a tuning in a
fixed nonresonant interval.
-/
#check @polyak.FareyPlateau.Edge.AdjacentData
#check @polyak.FareyPlateau.Edge.AdjacentData.function
#check @polyak.FareyPlateau.Edge.AdjacentData.finiteSymbol_eq

/-!
Article: Theorem 3.19 [thm:plateaujk]. The single-harmonic plateau of $j/k$.

Exact singleton plateau roof, classification of all regular singleton points, unique anchor and
rational boundary graph, plus the second-order subcritical interior test.

singleton_iff_roof is both directions for every actual tuning; aE and unrestricted aF are the
exact source thresholds. Connectedness/component and projected analyticity prove that the roof
is a plateau. The inverse representative b is constructible from coprimality
(Edge.inverse_exists). The a2 comparisons retain nonresonance.
-/
#check @polyak.FareyPlateau.singleton_iff_roof
#check @polyak.FareyPlateau.mem_singletonPlateau_iff
#check @polyak.FareyPlateau.singletonPlateau_eq_component
#check @polyak.FareyPlateau.singletonPlateau_in_gap
#check @polyak.FareyPlateau.singletonPlateau_extremals
#check @polyak.FareyPlateau.singletonPlateau_unique_anchor
#check @polyak.FareyPlateau.singletonPlateau_kappaBoundary
#check @polyak.FareyPlateau.singletonPlateau_projected_analytic
#check @polyak.FareyPlateau.Ray.a2_le_aF_nonresonant
#check @polyak.FareyPlateau.Ray.aF_le_edgeSymbol_maximum
#check @polyak.FareyPlateau.subcritical_source_interior

/-!
Article: Corollary 3.20 [cor:everyfarey]. A plateau at every Farey fraction.

Every reduced Farey fraction has a nonempty open connected singleton plateau and its unique
anchor/rational boundary; every gap has regular boundary points.

inverse_exists explicitly discharges the inverse representative assumption from j.Coprime k.
every_farey_plateau constructs the entire nonempty plateau; every_gap_regular_boundary supplies
the explicit fraction2/(2K+1). The graph and anchor statements are the general singleton results
from the preceding theorem.
-/
#check @polyak.FareyPlateau.Edge.inverse_exists
#check @polyak.FareyPlateau.every_farey_plateau
#check @polyak.FareyPlateau.every_gap_regular_boundary
#check @polyak.FareyPlateau.singletonPlateau_unique_anchor
#check @polyak.FareyPlateau.singletonPlateau_kappaBoundary

/-!
Article: Proposition 3.21 [prop:location]. Location of $\Pi_{j/k}$.

All four large-curvature limits for actual q(a,D), accumulation of the projected plateau, and
the exact undamped conjugate roots.

source_location works for arbitrary filters tending to infinite amplitude, stronger than a
single chosen sequence. The a>aE domain is eventually automatic at fixed D and is in particular
true on the singleton roof. The accumulation theorem constructs points of the actual plateau;
undamped_roots supplies the literal characteristic polynomial factorization.
-/
#check @polyak.FareyPlateau.source_location
#check @polyak.FareyPlateau.singletonPlateau_projection_accumulates
#check @polyak.FareyPlateau.undamped_roots

/-!
Article: Definition 3.22 [def:fanpairjk]. Fan pairs of $j/k$.

The signed primitive fan pair, exact offsets, coprimality of the near numerator and the
resonance/barycenter relation.

Fan.Data keeps integer L,J, sign=±1 and jL−kJ=sign, with L>k and 1≤j<k/2. The formulas near, far
and delta give the stated offsets; near_reduced proves gcd1. Since k≥3, the companion offset has
magnitude(k−1)|δ|>|δ|.
-/
#check @polyak.FareyPlateau.Fan.Data
#check @polyak.FareyPlateau.Fan.Data.near_reduced
#check @polyak.FareyPlateau.Fan.Data.near_displacement
#check @polyak.FareyPlateau.Fan.Data.far_displacement
#check @polyak.FareyPlateau.Fan.Data.barycenter

/-!
Article: Theorem 3.23 [thm:fanjk]. Fan pairs at a Farey fraction.

Both exact fan feasibility/nonexistence cutoffs, the little-o pair threshold, negative-curvature
advantage, sharp all-grid nondivisible-period penalty and a compact-uniform cutoff.

Actual theorems use an AdjacentData representation of the nonresonant slope; source
compact_uniform_fans constructs it for every tuning in a fixed adjacent interval. Arbitrary
nonzero carried measures are covered in the necessary half. Positivity of the displayed near
weight ensures that toNNReal preserves its value. The epsilon/cutoff statements are the literal
definitions of little-o and1+o(1), uniformly in the selected signed family.
-/
#check @polyak.FareyPlateau.FanAnalysis.Actual.fan_feasible
#check @polyak.FareyPlateau.FanAnalysis.Actual.fan_feasible_positive_mass
#check @polyak.FareyPlateau.FanAnalysis.Actual.fan_no_measure
#check @polyak.FareyPlateau.FanAnalysis.Actual.fan_pair_threshold_asymptotic
#check @polyak.FareyPlateau.FanAnalysis.Actual.negative_curvature_advantage
#check @polyak.FareyPlateau.FanAnalysis.Actual.negative_curvature_edge_interior
#check @polyak.FareyPlateau.FanAnalysis.Actual.nondiv_period_penalty
#check @polyak.FareyPlateau.FanAnalysis.Actual.fan_pair_threshold_ge_periodic
#check @polyak.FareyPlateau.FanAnalysis.compact_uniform_fans

/-!
Article: Theorem 3.24 [thm:tips]. Tips of the tongues.

A common open neighborhood of every first-tongue tip has the analytic exact periodic/full
threshold, singleton extremals, closed-tongue divergence description and three-lag regularity.

Tip.tips gives all conclusions on one common neighborhood V. The three lags are
literally{1,1+k,1−k}; the extremal iff includes the admissible atom at zero. The gap conclusion
is stronger, universal over any GapK in the neighborhood.
-/
#check @polyak.GapEdges.Tip.tips

/-!
Article: Theorem 3.25 [thm:BK]. The boundary in every gap.

Every gap contains both open signs and a separating nonempty boundary; positivity near the
diagonal and admissible corners, eventual negativity on every ray, and the full diagonal-side
projection neighborhood.

boundary_every_gap holds for every gap. path_meets_boundary applies to every continuous path
staying in the gap with opposite threshold signs at its endpoints. Boundary projection includes
exactly r=c_(K+1) and r=c_K for K≥3, retaining the K=2 lower-corner exception.
-/
#check @polyak.GapEdges.boundary_every_gap
#check @polyak.GapEdges.diagonal_projection_neighborhood
#check @polyak.GapEdges.path_meets_boundary
#check @polyak.GapEdges.diagonal_positive_neighborhood
#check @polyak.GapEdges.every_ray_eventually_negative
#check @polyak.GapEdges.corner_positive_neighborhood
#check @polyak.GapEdges.boundary_projection_neighborhood

/-!
Article: Lemma A.1 [lem:normalization]. Normalization.

A bijection between centered original functions and the normalized class, exact normalization of
iterates, and the Polyak recurrence coefficients.

normalizationEquiv uses inverses on the entire function classes. original_normalized_run derives
the error recurrence from the original gradient, minimizer and algorithm. The Polyak coefficient
identities require only0<μ<L.
-/
#check @polyak.normalizationEquiv
#check @polyak.Dynamics.original_normalized_run
#check @polyak.Dynamics.polyak_normalizedA
#check @polyak.Dynamics.polyak_normalizedB
#check @polyak.Dynamics.polyakBeta

/-!
Article: Theorem A.2 [thm:interpolation]. Interpolation on arbitrary sets.

Exact normalized interpolation equivalence for arbitrary index sets in any real Hilbert space,
with the origin datum.

interpolation_iff quantifies arbitrary E and I and a complete real inner-product space. The only
data assumptions are the indexed origin equalities, and TableFeasible unfolds to |Tij|≤Rij for
every i,j, for arbitrary indexed data on the Hilbert space.
-/
#check @polyak.Interpolation.interpolation_iff

/-!
Article: Lemma A.3 [lem:spectralinterp]. Exact spectral interpolation.

The exact spectral pair and origin interpolation slacks, and the equivalence between spectral
feasibility and one global normalized interpolant.

mixture_slack and mixture_star_slack retain the constants1/2 and1/4 and both signs.
mixture_interpolation_iff uses the continuous-mixture Hilbert space and applies to arbitrary
probability spectra.
-/
#check @polyak.Waves.mixture_slack
#check @polyak.Waves.mixture_star_slack
#check @polyak.Waves.mixture_interpolation_iff

/-!
Article: Lemma A.4 [lem:compact]. Compactness.

Weak compactness of fixed-exponent feasible pairs and compact parameter families for the Polyak
program, with |sinh v|≤1.

GeneralCompact treats an arbitrary continuous multiplier and fixed t. The Polyak over-compact
theorem bounds C analytically and the probability factor is compact. abs_u_le_one applies to
u=sinh v.
-/
#check @polyak.Spectral.isCompact_mixtureFeasible_pairs
#check @polyak.Spectral.isCompact_feasible_over
#check @polyak.Spectral.FeasibleU.abs_u_le_one

/-!
Article: Lemma A.5 [lem:envelope]. Growth envelope.

Finite submultiplicative free-segment envelope, its true Fekete root limit/infimum, positive
quadratic lower rate, original WN bound and spectral exponential lower bound.

envelope_le supplies the explicit finite majorant, while tendsto_envelope_root and
growthRate_eq_inf are proved using a lower bound. worstAll_le_envelope is the original from-rest
supremum inequality with exactly sqrt2. exp_le_envelope handles arbitrary feasible probability
spectra via the actual Hilbert mixture and finite-span reduction.
-/
#check @polyak.Growth.envelope_le
#check @polyak.Growth.envelope_submultiplicative
#check @polyak.Growth.exp_le_envelope
#check @polyak.Growth.tendsto_envelope_root
#check @polyak.Growth.growthRate_eq_inf
#check @polyak.Growth.growthRate_pos
#check @polyak.Growth.quadraticRate_le_growthRate
#check @polyak.Growth.worstAll_le_envelope

/-!
Article: Lemma A.6 [lem:energy]. Energy estimate.

One certificate-dependent positive constant and window w≥M′+2 control every finite segment and
every interior interval, with the two stated endpoint energies.

finite_segment_energy quantifies over RawSegment, which supplies values and gradients only at
interior positions, uniformly over arbitrary real Hilbert spaces. Endpoint completion and
finite-span compression are proved internally; the complete segment extends to a Run. Enlarging
the certified energy window gives w≥M′+2 and uses the article last-position index n (RawSegment
has n−1 transitions), with exactly j+w≤n and endpoint windows ending at n.
-/
#check @polyak.ArticleResults.finite_segment_energy

/-!
Article: Lemma A.7 [lem:plateau]. No strict certificate at the growth exponent.

No finite strict certificate exists at the actual free-segment growth exponent.

not_strictCertificate_at_growth directly negates Nonempty StrictCertificate for the true
multiplier at log growthRate. Its only nonzero-B assumption is implied by the standing positive
step and curvature gap.
-/
#check @polyak.Growth.not_strictCertificate_at_growth

/-!
Article: Lemma A.8 [lem:startup]. One-coordinate initialization.

A single from-rest objective in exactly2r+1 dimensions realizes the spectral exponential lower
bound for every time, with one auxiliary coordinate tending to zero.

exists_startup_model explicitly retains all r complex waves and the scalar response with a
proved limit0; exists_startup transports the complete space to the exact real dimension. The
strict minimizer slack is used only if t>0. iterate is definitionally initialized from rest.
-/
#check @polyak.Realization.exists_startup_model
#check @polyak.Realization.exists_startup

/-!
Article: Lemma A.9 [lem:vmono]. Symmetries and monotonicity in the twist.

Both feasibility symmetries, the explicit sinh-ratio scaling with the stated zero convention,
the feasible interval, evenness and universal V bound.

feasible_explicit_scale gives the stated sinh-ratio coefficient, including its zero convention.
The symmetry iff declarations retain the same probability measure. Interval/evenness/bound are
independent theorems about the actual feasible set.
-/
#check @polyak.Spectral.feasible_neg_t_iff
#check @polyak.Spectral.feasible_neg_v_iff
#check @polyak.ArticleResults.feasible_explicit_scale
#check @polyak.Spectral.twists_eq_Icc
#check @polyak.Spectral.V_even
#check @polyak.Spectral.V_le_arsinh_one

/-!
Article: Lemma A.10 [lem:finiteatoms]. Finite support and inactive tails.

Every noncritical optimal measure has finite support strictly inside the cosine interval, strict
minimizer slack and eventually strictly positive lags.

The carrier theorem gives a finite F simultaneously carrying every optimal pair at this T.
Strict minimizer and active-lag bounds hold for every optimal pair under T≠0.
-/
#check @polyak.Spectral.exists_actual_optimal_carrier
#check @polyak.Spectral.actual_optimal_strict_minimizer
#check @polyak.Spectral.actual_optimal_active_lags_bounded

/-!
Article: Lemma B.1 [lem:dualfactor]. Dual factorization.

Exact dual-symbol divided-difference factorization, alpha≥1, beta≥0 independent of u, and the
quantitative monotonicity inequality.

DualWeights gives finite nonnegative upper weights of sum 1. The polynomial coefficients depend
only on G, c and these weights; the factorization includes G=c=1.
-/
#check @polyak.Boundary.dual_factor
#check @polyak.Boundary.alpha_eq
#check @polyak.Boundary.beta_eq
#check @polyak.Boundary.alpha_ge_one
#check @polyak.Boundary.beta_nonneg
#check @polyak.Boundary.dualSymbol_mono

/-!
Article: Lemma B.2 [lem:spiralids]. Lag identities on the spiral.

Both exact spiral lag identities and E0=1+2G²,E1=E2=0.

The mean identities apply to every m≥1 with exactly g/G factors. kernel_zero,one,two are exact
algebraic identities including t=0.
-/
#check @polyak.Spiral.mean_lower_eq
#check @polyak.Spiral.mean_upper_eq
#check @polyak.Spiral.kernel_zero
#check @polyak.Spiral.kernel_one
#check @polyak.Spiral.kernel_two

/-!
Article: Lemma B.3 [lem:spiralkernel]. Positivity of the spiral kernel.

Every scaled spiral kernel for n≥3 is a natural-coefficient polynomial, with the exact
modulo-three constant term and strict positivity for positive s.

kernel_polynomial_representation uses index n−3 in ℕ[X], so all coefficients are literally
nonnegative. kernelPolynomialValue_zero preserves divisibility since n and n−3 have the same
residue mod3. The positivity and t≠0 specialization are separately proved.
-/
#check @polyak.Spiral.kernel_polynomial_representation
#check @polyak.Spiral.kernel_add_three_pos
#check @polyak.Spiral.kernel_at_zero
#check @polyak.Spiral.kernelPolynomialValue_pos
#check @polyak.Spiral.kernelPolynomialValue_zero

/-!
Article: Lemma B.4 [lem:tailsharp]. Amplitude identity and tail bound.

The sharp squared amplitude identity and both raw lag tails for every probability spectrum and
positive lag.

amplitude_identity uses ω=arccos c on[0,π], which is the surrounding frequency convention.
raw_lag_tail_both applies to arbitrary probability spectra and retains the corrections |C| and
2u² for every positive integer lag.
-/
#check @polyak.Boundary.amplitude_identity
#check @polyak.Boundary.raw_lag_tail_both

/-!
Article: Proposition B.5 [prop:spiralsub]. The spiral outside its regime.

The special spiral rate is strictly below the true rate in both outer and inner nonspiral
regimes.

spiral_strictly_suboptimal evaluates G at the logarithm of the spiral factor. It retains q∈(0,1)
and both strict regime alternatives; critical t_sp=0 is excluded by the regime inequalities.
-/
#check @polyak.Boundary.spiral_strictly_suboptimal

/-!
Article: Proposition B.6 [prop:strip]. Threshold strip.

Every feasible point lies in the golden-ratio strip, strictly away from t=0; the critical
three-cycle attains the endpoint.

The feasible-pair hypotheses are the original all-lag constraints; the strip is nonstrict at t=0
and strict for every t≠0. The actual spiral spectrum at t=0 is δ(-1/2), with charge 0 and
sinh(v)=1/2; V(0)=log φ identifies the printed endpoint.
-/
#check @polyak.Threshold.feasible_strip
#check @polyak.Threshold.feasible_strip_strict
#check @polyak.Spiral.feasibleU
#check @polyak.Spiral.critical_feasible

/-!
Article: Proposition B.7 [prop:p1]. The family $P_1$.

Complete optimality, one-atom geometry, reserve, monotonicity and strict slope bound of the
continued P₁ family.

The checked continued source branch supplies a one-atom spectrum, all lag inequalities,
optimality, the z³/4 minimizer reserve, exact quartic factorization and strict residual
positivity. The u(G) monotonicity and slope bound include the physical switch;
continuation_endpoint discharges the spiral join.
-/
#check @polyak.Boundary.P1.p1_point
#check @polyak.Boundary.P1.uOfG_strictMonoOn
#check @polyak.Boundary.P1.abs_boundaryDerivative_lt_one
#check @polyak.Boundary.P1.continuation_feasible
#check @polyak.Boundary.P1.abs_deriv_V_at_GW_lt_one

/-!
Article: Lemma B.8 [lem:p2curve]. The rational curve.

The rational parametrization satisfies P₂ identically and has the displayed exact u/G ratio.

These are the exact printed rational parametrization identity and u/G ratio. Their explicit
nonzero denominator assumptions are discharged on J by parameter_pos, rMinus_pos, qMinus_pos and
rPlus_pos.
-/
#check @polyak.Boundary.P2.curve_identity
#check @polyak.Boundary.P2.twist_ratio

/-!
Article: Definition B.9 [def:p2data]. Data of the arc.

The explicit P₂ arc data agree with the affine-remainder construction, whose denominator stays
nonzero.

The source definitions give the displayed W,a,b, ordered roots, mean, d and weight. The direct
bridge proves the two affine division remainders, their nonzero combined slope on all J, and
exact equality with the remainder-based definitions of mean and d. Probability spectrum
construction additionally uses ζ≥ζ₁, as required by the physical arc; raw data exist throughout
J.
-/
#check @polyak.Boundary.P2.W
#check @polyak.Boundary.P2.atomA
#check @polyak.Boundary.P2.atomB
#check @polyak.Boundary.P2.x
#check @polyak.Boundary.P2.y
#check @polyak.Boundary.P2.meanCosine
#check @polyak.Boundary.P2.d
#check @polyak.Boundary.P2.p
#check @polyak.ArticleResults.P2Data.lower_remainder
#check @polyak.ArticleResults.P2Data.upper_remainder
#check @polyak.ArticleResults.P2Data.remainder_denominator_nonzero
#check @polyak.ArticleResults.P2Data.remainder_data
#check @polyak.Boundary.P2.spectrum

/-!
Article: Lemma B.10 [lem:p2ids]. Algebraic identities on the arc.

Exact positive-weight and double-square identities, with the three active primal constraints of
P₂.

The exact K₆ sum of squares, complementary weight, dual double-square identity and all three
active primal equalities are proved for the actual source functions. On J the signs prove 0<W<1;
actual integral identities discharge the passage from polynomial moments to the two-atom
measure.
-/
#check @polyak.Boundary.P2.K6_sum_squares
#check @polyak.Boundary.P2.K6_pos
#check @polyak.Boundary.P2.one_sub_weight
#check @polyak.Boundary.P2.weight_bounds
#check @polyak.Boundary.P2.double_square_identity
#check @polyak.Boundary.P2.dualPolynomial_factor_p2
#check @polyak.Boundary.P2.dualPolynomial_nonneg
#check @polyak.Boundary.P2.active_constraints

/-!
Article: Lemma B.11 [lem:p2ends]. Endpoints.

Unique simple algebraic endpoints, spiral tangency and the exact Ga polynomial and rational
brackets.

Isolated roots have the stated rational brackets and simplicity; ζ₁ is the unique real cubic
root and ζa is unique in J. G(ζ₁)=G₁, the spiral contact identity and nonnegative separation,
Hₐ(Ga)=0, and uniqueness in the printed Ga bracket are source identities plus exact derivative
signs. The S₆ composition identity and numerator divisibility by N₁₂ identify the endpoint, with
uniqueness on all of J.
-/
#check @polyak.Boundary.P2.zeta1_bounds
#check @polyak.Boundary.P2.zetaA_bounds
#check @polyak.Boundary.P2.exists_zetaA
#check @polyak.Boundary.P2.zeta1_unique_real
#check @polyak.Boundary.P2.parameter_roots_simple
#check @polyak.Boundary.P2.GaRoot
#check @polyak.Boundary.P2.Ga_bounds
#check @polyak.Boundary.P2.G_zeta1
#check @polyak.Boundary.P2.Ha_Ga
#check @polyak.Boundary.P2.u_zeta1
#check @polyak.Boundary.P2.spiral_le
#check @polyak.Boundary.P2.touching_spiral
#check @polyak.ArticleResults.P2Data.switch_composition_identity
#check @polyak.ArticleResults.P2Data.endpoint_numerator_divisibility
#check @polyak.ArticleResults.P2Data.unique_arc_endpoint

/-!
Article: Lemma B.12 [lem:p2certs]. Sign certificates.

Every rational sign test has the stated strict sign, certified by literal single-center Taylor
dominance.

The complete 44 distinct factored sign polynomials, the 20 main source-linked RationalCode
numerator/denominator pairs, and all 14 remaining finite-lag pairs satisfy the literal
single-center Taylor criterion at 6789/4000 with radius 7/4000. Exact polynomial source
identities link the signs to the specified arc data.
-/
#check @polyak.ArticleResults.P2Data.displayed_taylor_tests
#check @polyak.Boundary.P2.signedTaylorCheck_positive
#check @polyak.Boundary.P2.G_lower_positive
#check @polyak.Boundary.P2.G_upper_positive
#check @polyak.Boundary.P2.u_lower_positive
#check @polyak.Boundary.P2.u_upper_positive
#check @polyak.Boundary.P2.midpoint_positive
#check @polyak.Boundary.P2.mean_root_factor_positive
#check @polyak.Boundary.P2.W_lower_positive
#check @polyak.Boundary.P2.W_upper_positive
#check @polyak.Boundary.P2.d_positive_positive
#check @polyak.Boundary.P2.gap_lower_positive
#check @polyak.Boundary.P2.gap_square_positive
#check @polyak.Boundary.P2.slope_positive_positive
#check @polyak.Boundary.P2.slope_lt_one_positive
#check @polyak.Boundary.P2.root_minus_outer_positive
#check @polyak.Boundary.P2.root_minus_inner_positive
#check @polyak.Boundary.P2.root_plus_inner_positive
#check @polyak.Boundary.P2.root_plus_outer_positive
#check @polyak.Boundary.P2.upper_five_factor_positive
#check @polyak.Boundary.P2.negativeEndpointDerivative_positive
#check @polyak.Numerics.taylor_expansion
#check @polyak.Numerics.taylor_variation_le
#check @polyak.ArticleResults.P2Data.finite_lag_taylor_tests
#check @polyak.ArticleResults.P2Data.all_factored_taylor_tests

/-!
Article: Theorem B.13 [thm:p2arc]. The arc $P_2$.

All seven geometric and all-lag feasibility conclusions on the closed P₂ arc, with optimality
and |V′|<1.

All seven conclusions hold on the complete closed physical arc: exact monotone parametrization,
strict rational boxes, probability masses with the unique zero at ζ₁, exact dual zero set,
minimizer reserve, complete active/inactive lag table (including the infinite tail), optimality
and the true boundary derivative at both joins.
-/
#check @polyak.Boundary.P2.p2_arc
#check @polyak.Boundary.P2.spectrum_optimal
#check @polyak.Boundary.P2.data_bounds
#check @polyak.Boundary.P2.G_strictAntiOn
#check @polyak.Boundary.P2.hasDerivAt_u
#check @polyak.Boundary.P2.dualPolynomial_zero_iff
#check @polyak.Boundary.P2.minimizer_gap
#check @polyak.Boundary.P2.infinite_tail_positive
#check @polyak.Boundary.P2.signedRaw_active_iff
#check @polyak.Boundary.P2.signedRaw_inactive_pos
#check @polyak.Boundary.P2.abs_deriv_V_lt_one_closed

/-!
Article: Theorem B.14 [thm:p5h0]. Closed form at $\kappa_c$.

The exact critical P₅ solution, reduced dual determinant, nonsingular Jacobian blocks and
rigorous decimal enclosures.

The actual regularized system vanishes at the explicitly defined algebraic point. Its primal and
dual blocks are the Jacobian blocks, both nonsingular; the dual reduction gives the exact
quintic consistency determinant. Algebraic definitions fix every displayed coordinate and
rigorous decimal brackets establish all printed approximations.
-/
#check @polyak.Boundary.P5.critical_system_verified
#check @polyak.Boundary.P5.critical_dual_reduced_0
#check @polyak.Boundary.P5.critical_dual_reduced_1
#check @polyak.Boundary.P5.critical_dual_reduced_2
#check @polyak.Boundary.P5.dualConsistency_det
#check @polyak.Boundary.P5.A₀
#check @polyak.Boundary.P5.B₀
#check @polyak.Boundary.P5.D₀
#check @polyak.Boundary.P5.P₀
#check @polyak.Boundary.P5.w2₀
#check @polyak.Boundary.P5.w3₀
#check @polyak.Boundary.P5.w5₀
#check @polyak.Boundary.P5.regularSystem_partial_isInvertible
#check @polyak.Boundary.P5.y₀_displayed_bounds
#check @polyak.Boundary.P5.A₀_displayed_bounds
#check @polyak.Boundary.P5.B₀_displayed_bounds
#check @polyak.Boundary.P5.D₀_displayed_bounds
#check @polyak.Boundary.P5.P₀_displayed_bounds
#check @polyak.Boundary.P5.w2₀_displayed_bounds
#check @polyak.Boundary.P5.w3₀_displayed_bounds
#check @polyak.Boundary.P5.w5₀_displayed_bounds
#check @polyak.Boundary.P5.critical_weights_relations
#check @polyak.Boundary.P5.critical_primal_equations
#check @polyak.Boundary.P5.critical_root_exists
#check @polyak.Boundary.P5.y₀_equation

/-!
Article: Proposition B.15 [prop:p5h0dual]. Dual nonnegativity at $\kappa_c$.

The critical normalized dual polynomial is nonnegative and vanishes exactly at its two contacts.

The factorization uses the normalized dual polynomial Q. Exact algebraic residual coefficients
and rational enclosures imply the strict quadratic reserve, nonnegativity and precisely the two
printed zeros.
-/
#check @polyak.Boundary.P5.critical_normalized_dual_factor
#check @polyak.Boundary.P5.critical_normalized_dual_nonneg
#check @polyak.Boundary.P5.critical_normalized_dual_zero_iff
#check @polyak.Boundary.P5.critical_dual_residual_pos
#check @polyak.Boundary.P5.q0₀_displayed_bounds
#check @polyak.Boundary.P5.q1₀_displayed_bounds
#check @polyak.Boundary.P5.q2₀_displayed_bounds
#check @polyak.Boundary.P5.critical_dual_residual_gap

/-!
Article: Proposition B.16 [prop:p5divslack]. First-order slacks.

Exact divided-slack limits, complete active-pair classification and the four smallest positive
values.

FirstSlack is the three residue-class formula in the statement. The derivative calculation
proves that it is the actual one-sided divided-slack limit; the active-pair predicate is exactly
{(1,−),(2,+),(3,+),(5,+)}. The complete infinite classification proves strict positivity
elsewhere and identifies the four smallest positive values with certified rounding.
-/
#check @polyak.Boundary.P5.firstSlack
#check @polyak.Boundary.P5.CriticalPair
#check @polyak.Boundary.P5.ActivePair
#check @polyak.Boundary.P5.firstSlack_eq_zero_iff
#check @polyak.Boundary.P5.firstSlack_positive_of_not_active
#check @polyak.Boundary.P5.tendsto_rawBranch_div
#check @polyak.Boundary.P5.tendsto_actualPrimal_div
#check @polyak.Boundary.P5.firstSlack_two_decimal_rounding
#check @polyak.Boundary.P5.firstSlack_printed_order
#check @polyak.Boundary.P5.firstSlack_smallest_four_iff

/-!
Article: Lemma B.17 [lem:p5tail]. Large lags near the three-cycle.

The listed central bounds imply strict positivity of both raw slacks for every lag m≥24.

TailBounds records the listed numerical, phase and amplitude hypotheses after p=hP and d=hD.
Under precisely these bounds both signed actual raw slacks are strictly positive for every m≥24.
The normalized-slack bridge has only positive radial denominators.
-/
#check @polyak.Boundary.P5.TailBounds
#check @polyak.Boundary.P5.twoAtomRaw_pos_of_tailBounds
#check @polyak.Boundary.P5.normalized_twoAtom_pos

/-!
Article: Theorem B.18 [thm:p5local]. Central family near $\kappa_c$.

A locally unique analytic central branch exists around a closed interval and gives the exact
optimal even analytic boundary near zero.

The analytic implicit-function branch through Z₀ solves the actual regularized system and is
locally unique near (0,Z₀). Shrinking the radius makes it analytic on a neighborhood of the
closed interval. All primal inequalities, dual optimality, the boundary formula, evenness,
analyticity at zero and V(0)=log φ follow from this local branch.
-/
#check @polyak.ArticleResults.central_branch_closed_neighborhood
#check @polyak.Boundary.P5.p5local
#check @polyak.Boundary.P5.critical_boundary_even_analytic

/-!
Article: Proposition B.19 [prop:p5arc]. The central family.

The full continued P₅ family is feasible and optimal, has strict slope bound and joins P₂
exactly.

The uniquely selected source branch on the entire closed physical domain is feasible and optimal
at every point, with all inactive lags controlled. Its endpoint equals the P₂ endpoint, and the
derivative estimate includes that join.
-/
#check @polyak.Boundary.P5.continuation_optimal
#check @polyak.Boundary.P5.continuation_feasible
#check @polyak.Boundary.P5.continuation_endpoint
#check @polyak.Boundary.P5.continuation_endpoint_u
#check @polyak.Boundary.P5.abs_deriv_V_lt_one_closed
#check @polyak.Boundary.P5.continuation_active_iff

/-!
Article: Lemma C.1 [lem:startupslack]. Slacks of the initial pairs.

Exact initialized-pair and minimizer-pair slack formulas, defect identities and strict charge
bound.

The interpolation pair identity includes the scalar startup reserve. The actual complex normal
form gives the printed quadratic and oscillatory terms and unchanged-value star identity.
Source-coordinate bridges prove both displayed defect formulas, Re Δ≤q, 0<g≤1/2 and the strict
bound |C|<1/2.
-/
#check @polyak.Realization.ExplicitSpiral.initial_pair_identity
#check @polyak.Realization.ExplicitSpiral.initial_star_identity
#check @polyak.Realization.ExplicitSpiral.actual_pair_normal_form
#check @polyak.Realization.ExplicitSpiral.source_gap_half
#check @polyak.ArticleResults.Startup.defect_norm_formula
#check @polyak.ArticleResults.Startup.defect_real_formula
#check @polyak.ArticleResults.Startup.source_gap_and_charge_bounds
#check @polyak.Realization.ExplicitSpiral.multiplier_gap
#check @polyak.Realization.ExplicitSpiral.response_source

/-!
Article: Lemma C.2 [lem:lineargap]. Linear gap.

Uniformly bounded finite certificates with lags at most five have a strict symbol gap
proportional to the exponent increment.

For every actual q∈(0,1), finite strict certificates exist at all sufficiently small positive
exponent increments. Their lags are ≤5, strict reserve is exactly aδ and every multiplier has
absolute value ≤1; the all-frequency strict symbol is a field of StrictCertificate. All
physical-branch and right-derivative hypotheses are discharged globally.
-/
#check @polyak.FiniteHorizon.actual_lineargap

/-!
Article: Lemma C.3 [lem:telescoping]. Telescoping with finite real filters.

The finite real-filter factorization gives an exact Hilbert-space telescoping identity and a
uniformly bounded width-six primitive.

The finite real Gram-factor structure is precisely the assumed sum-of-squared-filters identity.
For arbitrary Hilbert sequences, time, offset and distinguished index it yields the exact
telescoping equality, a width-six primitive and the uniform coefficient bound with cD=63,
independent of the factors and their number.
-/
#check @polyak.FiniteHorizon.banded_telescoping_offset7
#check @polyak.FiniteHorizon.banded_primitive_local7
#check @polyak.FiniteHorizon.banded_primitiveSize_le7
#check @polyak.FiniteHorizon.GramFactors

/-!
Article: Lemma C.4 [lem:plateauclass]. Plateau for classes of segments.

No zero-charge banded functional with strictly negative symbol is internally nonnegative on a
restriction-closed class of Euclidean H-segments at its exact rate.

SegmentClass records arbitrary classes of H-segments in R^d over all finite d, with exactly
closure under consecutive restriction. Given positive envelopes and a positive root limit r, the
theorem rules out every finite-width/offset zero-charge functional with strictly negative
Fourier symbol and internal nonnegativity. This applies to the Gram-window and zero-price
classes used below. The telescoping identity of C.3 holds in every real Hilbert space.
-/
#check @polyak.FiniteHorizon.not_general_banded_at_rate
#check @polyak.FiniteHorizon.SegmentClass

/-!
Article: Lemma C.5 [lem:continuation]. Continuation.

Every realizable window extends to an infinite segment, and every finite-memory segment extends
to an infinite H-segment.

Every point of the Gram window cone is realized by an actual interpolation run, and every finite
H-segment extends to an infinite H-run retaining its supplied data. The recurrence denominator
B≠0 holds for Polyak tuning, B=2q>0.
-/
#check @polyak.Growth.FiniteHorizon.windowCone_exists_run
#check @polyak.Growth.HSegment.exists_hRun

/-!
Article: Lemma C.6 [lem:relaxedrate]. Bounded memory preserves the rate.

Every sufficiently large fixed memory preserves the exact asymptotic growth rate.

The finite-memory growth rate equals exp(Tq) eventually in H for every q∈(0,1). The global
theorem explicitly selects one H₀≥7 and proves this equality for every H≥H₀, together with the
prices used in the subsequent lemmas.
-/
#check @polyak.FiniteHorizon.memory_rate_eq_global
#check @polyak.FiniteHorizon.exists_global_exact_price_and_kernel_decay

/-!
Article: Lemma C.7 [lem:prices]. Functionals above the rate.

Uniformly bounded prices above the rate satisfy the finite-step and infinite discounted-energy
inequalities.

The global family supplies actual banded source data with a fixed linear reserve and a common
coefficient bound, for every H≥7. The constructed linear window price has the stated finite-step
inequality, uniformly bounded coefficient norm, the infinite discounted-energy lower bound at
every restart, and nonnegativity on the realizable window cone. BandedSource7 is proved from
interpolation inequalities.
-/
#check @polyak.FiniteHorizon.exists_global_above_rate_data
#check @polyak.FiniteHorizon.windowPrice7_step
#check @polyak.FiniteHorizon.windowPrice7_size_le
#check @polyak.FiniteHorizon.windowPrice7_nonnegative
#check @polyak.FiniteHorizon.windowPrice7_contracts
#check @polyak.FiniteHorizon.AboveRateData7.run_series

/-!
Article: Lemma C.8 [lem:exactprice]. A functional at the exact rate.

An exact-rate nonnegative contracting price is strictly positive on every finite-feasible
stationary window.

One exact-rate price is nonnegative on the original cone and contracts on every actual finite
H-segment transition. Its strictly positive stationary-window lower bound holds for every
finite-feasible spectral pair; the exact stationary scaling transports the bound from center H
to every center k≥H, producing exp(2(k−5)T)/2.
-/
#check @polyak.FiniteHorizon.exists_global_exact_price_and_kernel_decay
#check @polyak.FiniteHorizon.PriceNonnegative
#check @polyak.FiniteHorizon.PriceContracts
#check @polyak.FiniteHorizon.stationary_price_lower_all_centers

/-!
Article: Lemma C.9 [lem:kernel]. A smaller rate on the kernel.

The zero-price kernel has a strictly smaller exponent, quantitatively and uniformly over
dimensions and blocks.

The exact price is accompanied by an exponent S<T and a uniform all-dimension, all-block bound C
exp(2(n−H)S) for every zero-price block. This quantitative estimate is stronger than the
asserted strict growth-rate inequality ρN<exp(T); zero-price forward invariance is proved from
nonnegativity and exact-rate contraction.
-/
#check @polyak.FiniteHorizon.exists_global_exact_price_and_kernel_decay
#check @polyak.FiniteHorizon.exists_kernel_segment_decay_of_stationary_price

/-!
Article: Lemma C.10 [lem:nearkernel]. Contraction near the kernel.

A sufficiently small price-to-trace ratio forces the stated contraction after one horizon p*≥H.

The globally obtained price admits p*≥H and η>0; NearKernelBound expands to the printed trace
contraction for every dimension, finite H-segment and admissible center. The stronger kernel
decay discharges the strict normalized-kernel contraction used by compactness.
-/
#check @polyak.FiniteHorizon.exists_global_exact_price_and_nearkernel
#check @polyak.Growth.FiniteHorizon.NearKernelBound

/-!
Article: Lemma D.1 [lem:dominant]. Dominant quadratic roots.

Dominant quadratic roots are real with the stated signs, distinctness and Vieta partner.

Tuning supplies exactly the quadratic stability domain, including β=0. Under ρQ>√β, the dominant
a-root is positive and all a-roots are real; the dominant b-root is negative, its real partner
is −β/ρb, and the strict root ordering proves distinctness.
-/
#check @polyak.General.Tuning.dominant_a_root
#check @polyak.General.Tuning.dominant_a_roots_real
#check @polyak.General.Tuning.dominant_b_root
#check @polyak.General.Tuning.dominant_b_roots_real
#check @polyak.General.Tuning.dominant_b_factor

/-!
Article: Lemma D.2 [lem:angle]. The angle at the threshold.

The threshold phase has the exact concave quadratic cotangent and phase-pi endpoint limits.

The angle is identified with the polar angle of the actual threshold symbol. The exact cotangent
quadratic, concavity and strictly negative endpoint values imply the two phase-pi endpoint
limits, including zero momentum.
-/
#check @polyak.General.Tuning.Xi
#check @polyak.General.Tuning.cot_angle
#check @polyak.General.Tuning.Xi_concave
#check @polyak.General.Tuning.Xi_one_neg
#check @polyak.General.Tuning.Xi_neg_one_neg
#check @polyak.General.Tuning.angle_pi
#check @polyak.General.Tuning.angle_tendsto_zero
#check @polyak.General.Tuning.threshold_polar

/-!
Article: Lemma D.3 [lem:cubic]. The lag-one cubic.

The source lag-one cubic has the displayed Chebyshev form, factorization, phase comparison and
cycle identity.

The direct bridge gives the literal Chebyshev cubic in P,Q,C,D,E; the source complex-real-part
identity identifies it with Hr. The factorization at r=1, both strict endpoint values, exact
angle comparison and the cycle-polynomial identity use the same L and κ′=x/y.
-/
#check @polyak.ArticleResults.cubic_chebyshev_formula
#check @polyak.General.Tuning.H_one
#check @polyak.General.Tuning.L_neg_one
#check @polyak.General.Tuning.L_one
#check @polyak.General.Tuning.L_neg_one_pos
#check @polyak.General.Tuning.L_one_pos
#check @polyak.General.Tuning.GTD_identity
#check @polyak.General.Tuning.H_complex
#check @polyak.General.Tuning.angle_gt_half_iff

/-!
Article: Lemma D.4 [lem:iqc]. The certificate as an integral quadratic constraint.

One explicit Hermitian trigonometric matrix gives both the true nonlinear integral IQC and the
exact linear-graph certificate symbol.

The explicit 2×2 trigonometric Hermitian matrix acts on the actual real nonlinear gradient
graph. The source-sign Fourier convention and coordinatewise Parseval identity give the literal
normalized integral IQC, while evaluating the same matrix on [1,m] gives the exact original
certificate symbol.
-/
#check @polyak.General.IQC.certificateSymbol
#check @polyak.General.IQC.certificateSymbol_isHermitian
#check @polyak.General.IQC.pairSymbol_trig
#check @polyak.General.IQC.certificateSymbol_source
#check @polyak.General.IQC.source_IQC_integral
#check @polyak.General.IQC.source_IQC_actual

/-!
Article: Lemma D.5 [lem:homotopy]. Homotopy.

The strict frequency gap and nonlinear homotopy IQCs give a uniform ℓ₂ bound for every causal
closed-loop solution.

A stable strictly proper causal scalar convolution and causal nonexpansive Δ form the actual
feedback system. The source-convention matrix IQC and strict frequency gap imply one uniform ℓ₂
bound for every τ∈[0,1] and forcing f; the theorem also establishes square summability and
uniqueness for solutions without presupposing that the solution lies in ℓ₂. Stable rational
convolution is a special case of the proved summable-filter theorem.
-/
#check @polyak.General.IQC.Feedback.ofConvolution
#check @polyak.General.IQC.Feedback.eq_run_of_equation
#check @polyak.General.IQC.Feedback.homotopy_source_frequency_solution_bound
#check @polyak.General.IQC.Feedback.homotopy_source_frequency_uniform_bound

/-!
Article: Lemma D.6 [lem:shift]. Weighted shift.

The uniform restarted energy estimate yields the exact two-step geometric decay constant and
floor(k/2) exponent.

The theorem has the literal C′=C₀ max(1,exp(−2t)), θ=C′/(1+C′), floor(k/2) bound. Its restart
hypotheses follow by shifting the same autonomous recursion with the same potential. The article
identifies varrho=exp(t); explicitly recording C₀>0 aligns the only sign premise.
-/
#check @polyak.General.IQC.weighted_shift

/-!
Article: Theorem D.7 [thm:mult]. Multiplier criterion.

One-sided multiplier signs imply strict convergence, the unit-rate bound and the inner-radius
bound in both lag orientations.

For finite nonnegative nonzero multiplier weights, the literal boundary ratios imply strict
convergence, the nonstrict unit bound, and the inner-radius bound. Both lower and upper lag
orientations are proved. The positive multiplier-mass premise is equivalent to the article’s
not-all-zero assumption; original_rate_eq transfers normalized rates to the stated original
heavy-ball rate.
-/
#check @polyak.General.Multipliers.lower_rate_lt_one
#check @polyak.General.Multipliers.upper_rate_lt_one
#check @polyak.General.Multipliers.lower_rate_le_one
#check @polyak.General.Multipliers.upper_rate_le_one
#check @polyak.General.Multipliers.lower_rate_le_radius
#check @polyak.General.Multipliers.upper_rate_le_radius
#check @polyak.General.Multipliers.mass_pos_iff_not_all_zero
#check @polyak.General.Multipliers.original_rate_eq

/-!
Article: Lemma D.8 [lem:symbols]. Symbols of one-sided certificates.

The four exponent-weighted one-sided symbols have the displayed exact factorized forms and
cancel the value charge.

All four symbols use the exact printed exponent-dependent lag weights and minimizer weights;
every C-charge cancellation is proved separately. The negative-time identities now hold
pointwise on every radius: at a zero of the characteristic polynomial both sides vanish, so the
former extra radial restriction has been removed in Lean. The sharp/unsharp unit-circle ratios
differ by a strictly positive factor and therefore have the same sign.
-/
#check @polyak.General.Multipliers.lower_positive_source_symbol
#check @polyak.General.Multipliers.upper_positive_source_symbol
#check @polyak.General.Multipliers.lower_cancel_positive
#check @polyak.General.Multipliers.lower_cancel_negative
#check @polyak.General.Multipliers.upper_cancel_positive
#check @polyak.General.Multipliers.upper_cancel_negative
#check @polyak.General.Multipliers.sharp_ratio_re_circle
#check @polyak.General.Multipliers.upper_sharp_ratio_re_circle
#check @polyak.ArticleResults.MultiplierSymbols.lower_negative_source_symbol
#check @polyak.ArticleResults.MultiplierSymbols.upper_negative_source_symbol

/-!
Article: Proposition D.9 [prop:single]. Single-harmonic spectra.

A reduced rational one-atom spectrum is feasible exactly when its phase is at most π/k.

For every reduced rational angle 2πj/k with 1≤j<k/2, actual threshold feasibility of the
one-atom probability measure with C=0 is equivalent to the exact phase bound Θ≤π/k. Both
directions include every signed integer lag.
-/
#check @polyak.General.Regions.single_harmonic_feasible_iff

/-!
Article: Lemma D.10 [lem:near1]. Near the unit circle.

Strict lag-one phase separation gives a positive inner annulus; cubic nonnegativity persists at
larger radii.

The angle hypothesis is exactly strict positivity of L on the closed cosine interval, including
its automatically positive endpoints. This yields a positive inner annulus for the source ratio
and monotonic persistence of nonnegativity of Hr on every larger radius below one.
-/
#check @polyak.General.Multipliers.exists_positive_ratio_inner_band
#check @polyak.General.Multipliers.source_radius_monotone
#check @polyak.General.Tuning.angle_gt_half_iff

/-!
Article: Corollary D.11 [cor:C]. Explicit regions.

Exact vertex/discriminant convergence regions, phase-locking contacts, rational tongue criteria
and dominant-root quadratic-rate tests.

The strict lag-one region has the exact β=0/vertex/discriminant criterion; its relative boundary
has an interior double contact and the stated locked frequencies. Rational tongue tests use the
actual phase curve. At either dominant real-root endpoint the exact quotient test characterizes
the quadratic-rate region, with convex versus concave branches and all endpoint sign conditions
discharged.
-/
#check @polyak.General.Regions.omegaOne_iff_explicit
#check @polyak.General.Regions.frontier_omegaOne_tangent
#check @polyak.General.Regions.frontier_tangency_angle
#check @polyak.General.Regions.phase_locked_on_convergence_boundary
#check @polyak.General.Regions.rational_angle_le_iff_explicit
#check @polyak.General.Regions.first_tongue_iff_L_nonpos
#check @polyak.General.Regions.dominant_positive_quadratic_regime_iff
#check @polyak.General.Regions.dominant_negative_quadratic_regime_iff

/-!
Article: Lemma D.12 [lem:Kmu]. Quotients at the dominant real roots.

The exact dominant-root cubic quotients have the stated leading coefficients, factorizations and
endpoint products.

The two literal real quadratic quotient formulas have leading coefficients ±4βr³ and the printed
endpoint products. The polynomial identities use a(r)=0 or b(−r)=0 in real expanded form. For
r>0 these are equivalent to the displayed x,y formulas by multiplying by r.
-/
#check @polyak.General.Regions.Kmu
#check @polyak.General.Regions.KL
#check @polyak.General.Regions.H_eq_Kmu
#check @polyak.General.Regions.H_eq_KL
#check @polyak.General.Regions.Kmu_neg_one
#check @polyak.General.Regions.KL_one

/-!
Article: Lemma E.1 [lem:ends]. Ends.

The shifted phase extends jointly real-analytically through both ends and has the exact
signed-lag endpoint jet.

One ambient real-analytic extension agrees with the actual shifted phase curve at every tuning,
shift and closed-interval frequency, giving a neighborhood of every compact subset. Endpoint
formulas hold on the negative-numerator branch, which includes neighborhoods of both ends; the
exact lag jet is 0,0,−n(n+2τq) for every signed lag and shift.
-/
#check @polyak.Levels.Geometry.shiftedAngle_end_formula
#check @polyak.Levels.Geometry.endAngle_eventually_eq_joint
#check @polyak.Levels.Geometry.joint_analytic_extension
#check @polyak.Levels.Geometry.endLag_zero
#check @polyak.Levels.Geometry.endLag_deriv_zero
#check @polyak.Levels.Geometry.endLag_second_zero

/-!
Article: Lemma E.2 [lem:alt]. Exact alternative.

Infeasibility of the full measure program is equivalent to a finite strict certificate using the
allowed signed lags.

For every curve and arbitrary signed-lag set, infeasibility of the full measure program is
equivalent to a finite strict symbol using only those lags. The compactness/separation proof
supplies the finite support of the certificate; normalization proves equivalence of finite
nonzero measures and probability formulations.
-/
#check @polyak.Levels.infeasible_iff_strictSymbol
#check @polyak.Levels.fpOn_iff_probability

/-!
Article: Proposition E.3 [prop:mono]. Monotonicity and phase floors.

Pointwise lowering preserves feasibility; strict certificates have the exact multiplier
phase-floor characterization and rational floors.

Interior pointwise lowering of an arbitrary phase curve preserves full feasibility. The actual
t=0 heavy-ball certificate is equivalent to a finite nonnegative signed-lag multiplier with
positive constant and the printed strict phase-floor inequality. Every rational floor is at
least π/k, and the limiting lag-one multiplier has floor ω/2 on the original domain.
-/
#check @polyak.Levels.fp_mono
#check @polyak.Levels.source_strictCertificate_iff_phaseFloors
#check @polyak.Levels.phaseFloor_rational_lower
#check @polyak.Levels.lagOne_phaseFloor

/-!
Article: Theorem E.4 [thm:convex]. Convexity.

The exact weighted second-derivative identity gives strict cotangent concavity, shifted-phase
convexity and compact interval sublevels.

The exact endpoint-weighted second-derivative identity yields strict concavity of the actual
cotangent hq for every tuning, including β=0. Every shifted phase has strictly positive second
derivative below π/2, and that closed sublevel is a compact convex subset of (0,π), hence an
interval or empty.
-/
#check @polyak.Levels.Geometry.cotangentSecond_endpoint_identity
#check @polyak.Levels.Geometry.cotangent_strictConcaveOn
#check @polyak.Levels.Geometry.shiftedAngle_second_pos
#check @polyak.Levels.Geometry.phaseBelow_convex
#check @polyak.Levels.Geometry.phaseBelow_isCompact

/-!
Article: Corollary E.5 [cor:dip]. Connected phase sublevel sets.

Every lattice line below π/2 has at most one dip; the closed dip is a compact interior interval
and the closure of a nonempty dip.

Every interval in the frequency domain where the lattice line is ≤π/2 has a convex strict phase
sublevel. Both dip variants are intervals; the closed dip is compact inside (0,π), and equals
the closure of the strict dip whenever that dip is nonempty. Empty and singleton tangency cases
are retained.
-/
#check @polyak.Levels.Geometry.one_dip_per_line
#check @polyak.Levels.Geometry.closedDip_ordConnected
#check @polyak.Levels.Geometry.dip_ordConnected
#check @polyak.Levels.Geometry.closedDip_isCompact
#check @polyak.Levels.Geometry.closedDip_interior_frequency
#check @polyak.Levels.Geometry.closedDip_eq_closure_dip

/-!
Article: Lemma E.6 [lem:dip]. Dip lemma.

Every full-program solution assigns strictly positive mass to the closed dip.

Every nonzero finite-measure solution of the full phase program gives strictly positive measure
to the closed dip. The minimizer constraint excludes concentration at zero, and the result
applies to every curve.
-/
#check @polyak.Levels.Geometry.full_solution_closedDip_mass_pos

/-!
Article: Proposition E.7 [prop:chart]. Coordinates of a gap.

Actual tunings admit the exact coefficient and ordered-root homeomorphisms, gap faces, rational
tongue graphs and amplitude limit.

All five clauses concern the actual tuning space: explicit inverse homeomorphisms, exact
ordered-root gap coordinates and connectedness, full relative closure and its
diagonal/tongue/stability faces, rational tongue graphs, and the infinite-condition-number
amplitude face. Subtype hypotheses unfold precisely to β>0, endpoint negativity, ordered window
roots and a>a₀, which imply the inverse-domain conditions.
-/
#check @polyak.Levels.Chart.coefficientHomeomorph
#check @polyak.Levels.Chart.gradientDescent_chart
#check @polyak.Levels.Chart.gap_iff_root_coordinates
#check @polyak.Levels.Chart.gapHomeomorph
#check @polyak.Levels.Chart.isConnected_gap
#check @polyak.Levels.Chart.closedDip_interval
#check @polyak.Levels.Chart.closure_gapParameterSet_iff
#check @polyak.Levels.Chart.diagonal_face_iff
#check @polyak.Levels.Chart.closed_gap_faces
#check @polyak.Levels.Chart.junction_phase_equations
#check @polyak.Levels.Chart.two_gap_stability_face
#check @polyak.Levels.Chart.rationalHeight_gt_baseline
#check @polyak.Levels.Chart.gap_tongue_graph
#check @polyak.Levels.Chart.amplitude_floor_iff_endpoint
#check @polyak.Levels.Chart.kappa_tendsto_of_coefficients
#check @polyak.Levels.Chart.Xi_one_identity

/-!
Article: Lemma E.8 [lem:Efactor].

For every tuning and nonzero z, the source Laurent expression factors exactly through the two
characteristic polynomials.

The exact complex Laurent factorization is proved for every actual tuning and every nonzero z.
The nonzero-z qualification makes the displayed z⁻¹ expression a Laurent identity; all
subsequent uses are on the unit circle.
-/
#check @polyak.Levels.Chart.E_factor

/-!
Article: Proposition E.9 [prop:monoform]. Monotone form.

The full program is equivalent to an integrable nonzero finite measure on the open interval;
larger measurable profiles preserve that same measure and the stated lag identity.

OpenMonotoneSolution includes finiteness, nonzeroness, integrability and both sets of moment
inequalities. shifted_open_monoform_iff uses measure push-forward and comap for arbitrary finite
measures. The support monotonicity theorem assumes precisely almost-everywhere strong
measurability, the support order and one upper bound; it proves integrability of the larger
profile and the exact difference identity.
-/
#check @polyak.Levels.Threshold.shifted_open_monoform_iff
#check @polyak.Levels.Threshold.OpenMonotoneSolution
#check @polyak.Levels.Threshold.MonotoneSolution.mono_on_support_aestronglyMeasurable

/-!
Article: Lemma E.10 [lem:kappa]. The condition number lowers the curve.

The exact condition-number derivative has a positive numerator, giving a uniform strict
cotangent increase.

XiAtKappa is the original Xi with only kappa varied. deriv_XiAtKappa has numerator
kappaNumerator and denominator y*(1-beta)*(kappa-1)^2. kappaNumerator_pos includes both
endpoints. Compactness yields a uniform Xi gap and sin(omega)<=1 turns it into the stated
cotangent gap; arccotangent is strictly decreasing.
-/
#check @polyak.Levels.deriv_XiAtKappa
#check @polyak.Levels.kappaNumerator_pos
#check @polyak.Levels.exists_uniform_cotangent_kappa_gap

/-!
Article: Proposition E.11 [prop:threshold]. Threshold.

Shift feasibility is exactly s ≥ σ; divergence is σ ≤ 0, the threshold epigraph is closed and
profile order shifts σ by the stated amount.

sigma is the infimum of a nonempty, bounded-below, closed upward set. shifted_fp_iff,
sigma_feasible, isClosed_sigma_epigraph, sigma_shift_compare and divergenceSet_iff_sigma_nonpos
prove feasibility at the threshold, the closed epigraph and the comparison statements.
-/
#check @polyak.Levels.Threshold.shifted_fp_iff
#check @polyak.Levels.Threshold.sigma_feasible
#check @polyak.Levels.Threshold.isClosed_sigma_epigraph
#check @polyak.Levels.Threshold.sigma_shift_compare
#check @polyak.Levels.divergenceSet_iff_sigma_nonpos

/-!
Article: Proposition E.12 [prop:periodic]. Periodic spectra.

Finite periodic residues characterize feasibility, and the prescribed positive atoms yield an
actual orbit in dimension 2r+1.

atomic_program_iff is an equivalence for the given atomic measure, including the minimizer
constraint and all k-1 nonzero residues. atomic_periodic_orbit_positive_count deletes exactly
the zero weights, preserves the positive count r, constructs a centered strongly convex smooth
function, gives a nonzero start, one positive distance constant for every iterate, and
convergence to a k-periodic orbit. The normalized tuning convention uses step 1 and curvature
endpoints q.x,q.y.
-/
#check @polyak.Levels.atomic_program_iff
#check @polyak.Levels.atomic_periodic_orbit_positive_count
#check @polyak.Levels.periodicFP_diverges

/-!
Article: Lemma E.13 [lem:pinid]. Pinning identity.

The shifted-lag identity, equality modulo the period and the derivative identity hold, including
one-sided endpoint derivatives.

pinning_identity is the literal cosine identity for arbitrary signed r,m. lag_mod_grid proves
residue reduction. pinning_derivative_closedInterval uses the usual differentiability relative
to [0,pi] and proves the displayed derivative increment, including the one-sided endpoint
derivatives.
-/
#check @polyak.Levels.pinning_identity
#check @polyak.Levels.lag_mod_grid
#check @polyak.Levels.pinning_derivative_closedInterval

/-!
Article: Lemma E.14 [lem:A-smooth]. Smoothing.

Smoothing gives the two stated moment bounds and the explicit local Fourier oscillation
estimate.

smoothing_constraint has exactly the coefficients D_0+3D_n+M2*mK*epsilon^2; smoothing_minimizer
has D_0+M2*mK*epsilon^2/2. The general phase hypotheses are the derivative and Taylor bounds
established for the fixed shifted tuning in the subsection. smoothDensity_measure identifies the
smooth density with the convolution measure. oscillation_bound identifies and bounds the actual
supremum D_n.
-/
#check @polyak.Global.Circle.smoothing_constraint
#check @polyak.Global.Circle.smoothing_minimizer
#check @polyak.Global.Kernels.oscillation_bound
#check @polyak.Global.Circle.smoothDensity_measure

/-!
Article: Lemma E.15 [lem:A-gain].

One positive gain constant works for every real frequency and smoothing scale.

exists_gain_constant quantifies one c>0 before both epsilon and xi and proves
c*min(epsilon^2*xi^2,1)<=1-kernelHat epsilon xi. The source bump and its moment definitions are
fixed earlier, with no numerical frequency cutoff.
-/
#check @polyak.Global.Kernels.exists_gain_constant

/-!
Article: Lemma E.16 [lem:A-alias]. Aliasing.

Smooth even sampled densities are symmetric, their moments are exactly periodic, and aliasing is
uniformly O(L⁻²) in the half-period range.

aliasing_lemma proves all three clauses for the actual sampleMeasure. Haar is normalized in
Lean, so the Lean density is 2*pi times the paper Lebesgue density and the weights f/L equal the
displayed paper weights 2*pi*f_source/L. Theta is already the fixed shifted tuning in this
subsection, with its piecewise analytic phase bounds.
-/
#check @polyak.Global.Sampling.aliasing_lemma

/-!
Article: Lemma E.17 [lem:A-sampling]. Sampling.

Nondegeneracy below the exact larger-root cutoff implies feasibility for every sufficiently
large period.

sourceCutoff is lagCutoff of exactly the three polynomial coefficients in the statement.
sampling_lemma requires all nonzero lags nonnegative, a strictly positive minimizer moment and
strict low lags below this cutoff. It concludes existence of L0 followed by every L>=L0.
canonicalM1_source_sup and canonicalM2_source_sup identify the constants with the source
derivative suprema.
-/
#check @polyak.Global.Sampling.sourceCutoff
#check @polyak.Global.Sampling.sampling_lemma
#check @polyak.Global.Sampling.canonicalM1_source_sup
#check @polyak.Global.Sampling.canonicalM2_source_sup

/-!
Article: Corollary E.18 [cor:kappaL]. Periodic thresholds of the condition number.

The periodic condition threshold lies in (1,∞], its epigraph is the periodic divergence set, and
their infimum is the full threshold.

periodic_condition_threshold gives the condition-number threshold.
kappaBoundary_eq_iInf_kappaPeriodic applies periodic sampling to identify their infimum.
kappaPeriodic_gt_one includes the possible infinite endpoint.
-/
#check @polyak.Global.Threshold.periodic_condition_threshold
#check @polyak.Global.Threshold.kappaBoundary_eq_iInf_kappaPeriodic
#check @polyak.Global.Threshold.kappaPeriodic_gt_one

/-!
Article: Theorem E.19 [thm:limitsymbol]. Limit symbol.

At every attained full threshold, one normalized summable nonpositive symbol has maximum zero
and controls every extremal by complementary slackness.

limit_symbol constructs a LimitSymbol with max_zero, carried and support_zero for every finite
ProgramSolution, and both lag and minimizer slackness. Weights supplies nonnegativity,
summability and residual gamma; normalized and continuous expose the two requested properties
directly.
-/
#check @polyak.Global.Symbols.limit_symbol
#check @polyak.Global.Symbols.LimitSymbol.normalized
#check @polyak.Global.Symbols.LimitSymbol.continuous
#check @polyak.Global.Symbols.LimitSymbol

/-!
Article: Lemma E.20 [lem:A-limit]. Limits of symbols.

Normalized finite nonpositive symbols admit a coefficientwise subsequence; escaped mass is
retained in γ, with all-extremal slackness whenever the limit program is feasible.

limits_of_normalized_finite_symbols accepts arbitrary signed lag subsets and uniformly
convergent Curve objects. Its coefficients are the actual finite symbol coefficients. Weights
has sum<=1 and gamma:=1-tsum; the returned LimitSymbol carries max-zero and all
complementary-slackness clauses. The residual gamma_* includes mass escaping to unbounded lag
indices.
-/
#check @polyak.Global.Symbols.limits_of_normalized_finite_symbols
#check @polyak.Global.Symbols.Weights

/-!
Article: Lemma F.1 [lem:positions]. Positions.

Grid lag values are the signed position function; its signs, modular permutation and transported
residue classes are exact.

lag_at_grid_eq_positionValue and the two sign equivalences cover (a)-(b), with value zero at
position zero by unfolding positionValue. position_mul_bijective proves the ZMod bijection. The
remaining four modular identities identify positions 1,0,j with the parent, period and lag-one
classes, and transport companions by the actual inverse b.
-/
#check @polyak.Farey.lag_at_grid_eq_positionValue
#check @polyak.Farey.positionValue_neg_iff
#check @polyak.Farey.positionValue_eq_zero_iff
#check @polyak.Farey.position_mul_bijective
#check @polyak.Farey.position_one_class
#check @polyak.Farey.position_zero_class
#check @polyak.Farey.position_lag_one
#check @polyak.Farey.residue_transport_of_inverse

/-!
Article: Theorem F.2 [thm:lattice]. Lattice lines.

Negative and zero lag values correspond exactly to the lattice strips and lines; rational atoms
and the level-one half-plane have the stated coordinates.

curve_signed_lag_neg_iff gives the open strip criterion for every Curve and signed lag.
signed_lag_zero_iff gives exactly the two integer line families. rational_lattice_point and
rational_ray_scale/rational_ray_beyond_iff establish the incidence and radial ordering;
omegaOne_iff_halfplane is the original tuning region equivalence.
-/
#check @polyak.Levels.Lattice.curve_signed_lag_neg_iff
#check @polyak.Levels.Lattice.signed_lag_zero_iff
#check @polyak.Levels.Lattice.rational_lattice_point
#check @polyak.Levels.Lattice.omegaOne_iff_halfplane
#check @polyak.Levels.Lattice.rational_ray_scale
#check @polyak.Levels.Lattice.rational_ray_beyond_iff

/-!
Article: Theorem F.3 [thm:farey]. Farey parents and first violations.

Farey parent lags are the two small incidence solutions, and the complete residue violation test
characterizes rational single atoms.

FareyParents contains the positive denominators, mediant identities and unimodular determinant
of the actual parents. Incidence modulo k and |n|<k have the exact signed solutions b,-d.
rational_lag_neg_iff_ceil proves the complete set of bad positions;
first_violations_parent_class is its first phase interval. rational_atom_program_iff includes
the minimizer inequality automatically.
-/
#check @polyak.Levels.Lattice.incidence_iff_zmod_inverse
#check @polyak.Levels.Lattice.FareyParents.small_incidence_iff
#check @polyak.Levels.Lattice.FareyParents.lower_other_parent
#check @polyak.Levels.Lattice.FareyParents.upper_other_parent
#check @polyak.Levels.Lattice.rational_lag_neg_iff_ceil
#check @polyak.Levels.Lattice.first_violations_parent_class
#check @polyak.Levels.Lattice.rational_atom_program_iff

/-!
Article: Lemma F.4 [lem:tongue]. The tongue of a fraction.

The inverse-kappa identity yields the exact rational tongue epigraph, infinity convention and
full-boundary upper bound.

Xi_inverse_kappa uses the same kappaNumerator. rational_tongue_epigraph is an equivalence for
the actual phase inequality. rationalTongue_eq_top covers nonpositive denominator; positive
denominator unfolds to exactly the displayed quotient. kappaNumerator_at_cos rewrites 1-cos^2 as
sin^2. The boundary bound requires the fraction to be reduced, as in the surrounding
fixed-fraction convention.
-/
#check @polyak.Farey.Xi_inverse_kappa
#check @polyak.Farey.rational_tongue_epigraph
#check @polyak.Farey.rationalTongue_eq_top
#check @polyak.Farey.kappaNumerator_at_cos
#check @polyak.Farey.kappaBoundary_le_rationalTongue

/-!
Article: Proposition F.5 [prop:farey]. Farey localization.

Every feasible periodic spectrum in a gap has a reduced rational anchor in the stated window,
with the denominator bound and phase alternatives.

farey_localization quantifies over the given finite Borel measure and its actual grid carrier.
It produces a positive-mass Anchor, primitive j,k with k dividing L, the strict window, k>=2K+1,
phase<=pi*j/k and the strict pi/k inequality unless the single atom is itself feasible.
-/
#check @polyak.Farey.gap_closedDip_window
#check @polyak.Farey.farey_localization

/-!
Article: Definition F.6 [def:anchor]. Anchors.

Anchors are exactly positive-mass atoms in the closed dip.

Anchor unfolds to omega in the original closedDip and 0<w{omega}. Feasibility is the surrounding
premise when applying this positive-mass atom predicate to solutions of the full program.
-/
#check @polyak.Farey.Anchor

/-!
Article: Lemma F.7 [lem:fan]. Fan geometry.

The lower fan has the stated Farey parents and lattice lines, with both displayed congruences.

spineParents explicitly builds ParentData for p/(pK+1), so its unimodularity and mediant fields
prove the parent claim. lower_spine_parent_order gives the strict ordering for p>=2. The lattice
equations and fan_anchor_inverse/fan_previous_den_congruence give the signed lag -K and the
second lag class exactly. The p>=2 range is fixed by the fan convention.
-/
#check @polyak.Farey.lower_spine_parent_order
#check @polyak.Farey.spineParents
#check @polyak.Farey.lower_spine_lattice
#check @polyak.Farey.line_through_first_point
#check @polyak.Farey.first_point_line_fan
#check @polyak.Farey.fan_anchor_inverse
#check @polyak.Farey.fan_previous_den_congruence

/-!
Article: Lemma F.8 [lem:record]. Record lows and Farey parents.

A residue record is equivalent to coprimality and the right-parent height cutoff; its preceding
minimum is explicit and unique.

record_low_residue_iff defines i and m from actual Euclidean residue/division, matching the
article setup. RightParent has r*j-m*rprime=1 and 1<=rprime<j. record_low_unique_minimum proves
the integer quotient (k+lprime*i)/j and unique minimizer lprime, with all earlier residues
quantified.
-/
#check @polyak.Farey.record_low_residue_iff
#check @polyak.Farey.record_low_unique_minimum

/-!
Article: Theorem F.9 [thm:twoatom]. Two-atom combs.

All-lag two-atom feasibility is exactly selection plus the closed mass-ratio interval; Farey and
both fan selection rules retain every allowed depth.

Comb.ofCurve constructs the finite CombData solely from the article k,j,i,t and phase
hypotheses, deriving the companion transport. Negative-position lemmas identify the exact
maxima/minima in the displayed ratios. lag_feasible_iff, mass_ratio_iff and twoatom_criterion
cover existence, all ratios and the minimizer moment. full_selection_iff/shallow_selection and
the six SpineBridge statements derive both signed multipliers and all-depth selection rules from
these data.
-/
#check @polyak.Farey.Comb.ofCurve
#check @polyak.Farey.CombData.anchor_negative_positions
#check @polyak.Farey.CombData.companion_negative_positions
#check @polyak.Farey.Comb.periodic_of_criterion
#check @polyak.Farey.Comb.lag_feasible_iff
#check @polyak.Farey.Comb.mass_ratio_iff
#check @polyak.Farey.Comb.twoatom_criterion
#check @polyak.Farey.CombData.full_selection_iff
#check @polyak.Farey.CombData.shallow_selection
#check @polyak.Farey.CombData.first_spine_multiplier
#check @polyak.Farey.CombData.first_spine_selection
#check @polyak.Farey.CombData.first_spine_forces
#check @polyak.Farey.CombData.second_spine_multiplier
#check @polyak.Farey.CombData.second_spine_selection
#check @polyak.Farey.CombData.second_spine_full

/-!
Article: Theorem F.10 [thm:fan-div]. Fan tongues.

The full finite fan program yields an actual periodic orbit; the two-lag determinant and the p=2
remaining-lag criterion are exact.

fan_div_a uses every grid weight and returns dimension 2r+1 for its positive count, with an
actual orbit and rate>=1. fan_div_b proves all four signs, determinant equivalence, p<=K+1 and
the automatic half-angle bound. fan_divergence_admissible_ratio supplies the
remaining-lag/minimizer implication in (b). fan_div_c proves all remaining lags automatically
and the iff involving the displayed fanP2Expression, including the non-strict upper phase
endpoints.
-/
#check @polyak.Farey.fan_div_a
#check @polyak.Farey.fan_div_b
#check @polyak.Farey.fan_div_c
#check @polyak.Farey.fan_divergence_admissible_ratio
#check @polyak.Farey.fanP2Expression

/-!
Article: Theorem F.11 [thm:fan-conv]. Fan-lag certificates.

A finite strict fan-polynomial certificate implies ρ<1; the two-lag specialization is the
displayed one.

fan_formula_rate_lt_one assumes only finite nonnegative weights, gamma>0 and the strict source
polynomial inequality on the closed cosine interval. The tuning structure includes the
quadratic-stability region. twoLag_fan_left/right evaluate the family at P={0},N={1},weights 1,r
exactly.
-/
#check @polyak.Farey.Certificates.fan_formula_rate_lt_one
#check @polyak.Farey.Certificates.twoLag_fan_left
#check @polyak.Farey.Certificates.twoLag_fan_right

/-!
Article: Lemma F.12 [lem:pin]. Pinning lags.

The paired fan lag constraints coincide on periodic measures and their differences have the two
exact first derivatives.

fan_congruences gives the literal signed lag identities. periodic_integral_lag_D/E prove
equality after integration for every carried finite measure. pinning_lemma gives both zeros and
derivatives for a differentiable curve at the grid point; its derivative assumptions match the
differentiation in the statement.
-/
#check @polyak.Farey.Pinning.fan_congruences
#check @polyak.Farey.Pinning.periodic_integral_lag_D
#check @polyak.Farey.Pinning.periodic_integral_lag_E
#check @polyak.Farey.Pinning.pinning_lemma

/-!
Article: Definition G.1 [def:regular]. Regular periodic point.

RegularData encodes exactly the positive finite primal/dual data and conditions R1–R3;
RegularPoint is existence of those data.

The same Fin d indexes support and active residue classes, encoding |A|=|S|. Injectivity,
normalization and primal rank d-1 are literal fields. The zero residue is retained by classes
and class_pair. dual_strict, support_curvature, endpoint_curvature and pinning_pos are precisely
R2; class_pair and pinning_det encode R3.
-/
#check @polyak.ModeLocking.RegularData
#check @polyak.ModeLocking.RegularPoint

/-!
Article: Corollary G.2 [cor:plateau]. Open plateaus.

Regularity is open; every boundary plateau has fixed support, least period and tight classes, an
analytic boundary and one fixed determinant equation.

plateau is the actual connectedComponentIn of the relatively open regular subset of the actual
divergence frontier. isOpen_regularTunings/isOpen_regularBoundary discharge openness.
plateau_labels covers all three intrinsic labels. plateau_fixed_determinant_zero retains one
fixed ordering over the whole component, and analyticOnNhd_ambientKappaBoundary_plateau gives
the actual projected boundary function. plateau_unique_anchor quantifies over every full-program
solution with the single-window-support premise.
-/
#check @polyak.ModeLocking.Plateaus.isOpen_regularTunings
#check @polyak.ModeLocking.Plateaus.isOpen_regularBoundary
#check @polyak.ModeLocking.Plateaus.plateau_labels
#check @polyak.ModeLocking.Plateaus.plateau_unique_anchor
#check @polyak.ModeLocking.Plateaus.plateau_fixed_determinant_zero
#check @polyak.ModeLocking.Plateaus.analyticOnNhd_ambientKappaBoundary_plateau
#check @polyak.ModeLocking.Plateaus.plateau

/-!
Article: Corollary G.3 [cor:periods]. Periods on a plateau.

The exact periodic periods are the multiples of the intrinsic least support denominator, and fan
feasibility is equivalent to coprimality with K.

least_common_support_denominator proves minimality of the period supplied by any genuine
RegularData. periodic_iff_dvd and fan_periodic_iff_coprime apply at its attained threshold,
hence at shift zero on the boundary. The finite periodic grid and finite atomic representation
identify the fan program with that periodic feasibility.
-/
#check @polyak.ModeLocking.RegularData.least_common_support_denominator
#check @polyak.ModeLocking.RegularData.periodic_iff_dvd
#check @polyak.ModeLocking.RegularData.fan_periodic_iff_coprime

/-!
Article: Theorem G.4 [thm:bdry]. Structure of a boundary point.

All five boundary clauses hold: common limit symbol, dip mass, periodic anchors, nonperiodic
alternatives and periodic nonregular plateau ends.

boundary_limit_symbol has all-extremal slackness in LimitSymbol. The dip and anchor statements
concern every actual extremal. nonperiodic_extremal_alternatives proves the complete disjunction
including a nonatomic restriction; nonperiodic_boundary_thresholds proves sigma_L->0.
source_plateau_ambient_closure uses ambient closure and fixed intrinsic support;
source_plateau_ends derives periodicity and nonregularity for the ambient plateau endpoints.
-/
#check @polyak.ModeLocking.boundary_limit_symbol
#check @polyak.ModeLocking.boundary_closedDip
#check @polyak.ModeLocking.boundary_periodic_iff
#check @polyak.ModeLocking.boundary_periodic_anchor
#check @polyak.ModeLocking.boundary_symbol_meets_dip
#check @polyak.ModeLocking.nonperiodic_extremal_alternatives
#check @polyak.ModeLocking.nonperiodic_boundary_thresholds
#check @polyak.ModeLocking.source_plateau_ambient_closure
#check @polyak.ModeLocking.source_plateau_ends

/-!
Article: Proposition G.5 [prop:heavy]. Heavy atoms move continuously.

One common atom above mass 1/2 moves continuously; it is rational at periodic points, and
nonconstant motion yields uncountably many nonperiodic points.

heavy_atoms_move_continuously quantifies over ALL finite Borel extremals with zero atom at 0 and
total positive-frequency mass one, exactly NormalizedExtremalMeasure. Its hypothesis is one
common lower bound m>1/2 on the connected set. The conclusion constructs the positive-frequency
position, common-mass property, continuity, rationality and uncountability. Nonconstant motion
remains an explicit premise only of the final implication.
-/
#check @polyak.ModeLocking.NormalizedExtremalMeasure
#check @polyak.ModeLocking.heavy_atoms_move_continuously

/-!
Article: Proposition G.6 [prop:polycert]. Polynomial certificates.

Strict finite signed-lag symbols are equivalent to the displayed strict polynomial inequality on
[-1,1].

polynomial_certificates has the fully expanded Chebyshev T and signed U expression, with
nonnegative weights and gamma. strict_symbol_polynomial_iff additionally identifies strictness
with a single uniform epsilon>0. Both endpoints are included; gamma=0 is correctly impossible
for a strict symbol.
-/
#check @polyak.ModeLocking.Localization.polynomial_certificates
#check @polyak.ModeLocking.Localization.strict_symbol_polynomial_iff

/-!
Article: Theorem G.7 [thm:tightclass]. Exact relaxations near a regular point.

Near a regular point all containing lag relaxations are exact, the support period is least, and
all four convergence tests agree.

least_common_support_denominator proves (a). all_supersets_exact_near removes even an artificial
nonzero-lag restriction by erasing the identically zero lag, so (b) holds for every Nprime
containing N. exact_relaxations_near supplies sigma_L as well; local_convergence_criterion gives
the finite/full periodic/positive shift equivalents in (c). The neighborhood arises from proved
regular persistence.
-/
#check @polyak.ModeLocking.RegularData.least_common_support_denominator
#check @polyak.ModeLocking.RegularData.all_supersets_exact_near
#check @polyak.ModeLocking.RegularData.exact_relaxations_near
#check @polyak.ModeLocking.RegularData.local_convergence_criterion

/-!
Article: Theorem G.8 [thm:qlock]. Quantitative locking.

The exact locking potential has the stated endpoint and quadratic behavior; feasible measures
satisfy the mean/infimum bound and periodic thresholds obey the sharp quadratic penalty.

The potential and budget are the actual lag-symbol quotients; regular_pinning_pos is proved for
every positive frequency. potential_quadratic_limit exposes the exact coefficient, and endpoint
limits diverge to +infinity. regular_average_locking and potential_inf_le_average retain
arbitrary finite Borel solutions. quantitative_locking_relative gives the rigorous epsilon-delta
form of the 1-o(1) bound; gridSupportDistance_lcm proves the rational lower bound.
-/
#check @polyak.ModeLocking.Localization.continuousOn_regularPotential
#check @polyak.ModeLocking.Localization.regularPotential_pos
#check @polyak.ModeLocking.Localization.regularPotential_zero
#check @polyak.ModeLocking.Localization.potential_quadratic_limit
#check @polyak.ModeLocking.Localization.regularPotential_tendsto_at_zero
#check @polyak.ModeLocking.Localization.regularPotential_tendsto_at_pi
#check @polyak.ModeLocking.Localization.feasible_charges_interior
#check @polyak.ModeLocking.Localization.regular_average_locking
#check @polyak.ModeLocking.Localization.potential_inf_le_average
#check @polyak.ModeLocking.Localization.quantitative_locking_relative
#check @polyak.ModeLocking.Localization.gridSupportDistance_lcm

/-!
Article: Theorem G.9 [thm:local]. Localization.

An actual normalized finite threshold symbol gives the endpoint-resolved localization inequality
and the displayed bound for each positive atom.

finite_threshold_symbol constructs the coefficients at sigma_N. local_for_program uses the
original measure constraints to prove the three endpoint/interior terms. sineRatio_interior
identifies its continuous extension with the displayed quotient. atom_localization has the
actual positive atom mass and yields the exact factor 2*(s-t)*total/mass times the sine ratio;
normalization and symbol sign come from the constructed witness.
-/
#check @polyak.ModeLocking.Localization.finite_threshold_symbol
#check @polyak.ModeLocking.Localization.local_for_program
#check @polyak.ModeLocking.Localization.atom_localization
#check @polyak.ModeLocking.Localization.sineRatio_interior

/-!
Article: Corollary G.10 [cor:local]. Quadratic localization.

Finitely many nondegenerate interior symbol zeros imply one uniform quadratic distance
localization bound for every finite feasible measure and every s≥σ_N.

quadratic_localization assumes precisely the closed-interval sign, finite complete interior zero
set, negative second derivatives there, T(pi)<0 and negative Tsecond(0) when gamma=0. It
constructs c>0 before s and w, proving the displayed total-mass bound with the exact distance to
{0} union Z. The statement is stronger in allowing any finite measure with a nonnegative
integrated symbol.
-/
#check @polyak.ModeLocking.Localization.quadratic_localization

/-!
Article: Proposition G.11 [prop:decouple]. Decoupling.

The two-lag feasibility product, admissible ratio interval, dual coefficients and complete dual
zero set follow from the stated attained minus maximum.

PlusMaximum includes its empty-plus-set value zero and a attaining point in the nonempty case;
exists_plusMaximum derives it from NoCommonNonnegative. decoupling_feasible_iff additionally
assumes exactly the stated attained minus maximum with positive cosine. The ratio interval
equivalences concern the actual lag values. decoupling_dual proves gamma=0, both positive lag
coefficients, the reciprocal maxima and both exact zero families for every nontrivial
nonpositive symbol.
-/
#check @polyak.ModeLocking.TwoLag.exists_plusMaximum
#check @polyak.ModeLocking.TwoLag.decoupling_feasible_iff
#check @polyak.ModeLocking.TwoLag.pair_ratio_constraints_iff
#check @polyak.ModeLocking.TwoLag.pair_interval_nonempty_iff
#check @polyak.ModeLocking.TwoLag.decoupling_dual

/-!
Article: Theorem G.12 [thm:exact]. Exact two-lag points.

The primary E1–E4 data construct full regularity with the six displayed lags, exact
full/periodic/two-lag thresholds and the actual extremal/continuation conclusions.

ExactData contains only E1–E4, the frequency interior/grid bounds, K>=2 and L>=K+2. Its
inactive/minimizer fields are E3 after choosing the canonical positive null-vector weights
(-B,A). exists_regularData constructs the six-lag certificate, including positive pinning
perturbation. The three sigma equalities are unconditional consequences of these data;
RegularData.extremal_iff and mode_locking then give all-extremal uniqueness and local
continuation.
-/
#check @polyak.ModeLocking.TwoLag.ExactData
#check @polyak.ModeLocking.TwoLag.ExactData.exists_regularData
#check @polyak.ModeLocking.TwoLag.ExactData.sigma_eq
#check @polyak.ModeLocking.TwoLag.ExactData.sigmaPeriodic_eq
#check @polyak.ModeLocking.TwoLag.ExactData.sigmaPair_eq
#check @polyak.ModeLocking.RegularData.mode_locking
#check @polyak.ModeLocking.RegularData.extremal_iff

/-!
Article: Corollary G.13 [cor:exactdD]. Exact points on the boundary.

A zero-shift exact point lies on an analytic boundary plateau satisfying the same two-frequency
determinant throughout, with the unique anchor under the extra window separation.

exact_boundary_corollary derives gap membership and the actual divergence boundary from the
first contact window; it gives the actual projected open connected analytic plateau and the
determinant for every point of that plateau. plateau_unique_anchor retains exactly the
additional second-frequency-below-window premise and quantifies over every full-program measure.
-/
#check @polyak.ModeLocking.TwoLag.ExactData.exact_boundary_corollary
#check @polyak.ModeLocking.TwoLag.ExactData.plateau_unique_anchor

/-!
Article: Proposition G.14 [prop:twolagtangency]. Two-lag symbols as double tangencies.

Two-lag symbols factor exactly; the complete sign/contact/curvature equivalence, Hermite
compatibility and contact lag signs are proved.

LagTangencies and RationalTangencies are the literal two sides of (b), including the strict
rational inequality at c=1 that encodes the endpoint curvature. double_tangencies_iff proves
both directions for any K>=2. Hermite_of_lag_tangencies derives slopes and G=0;
Hermite_quadratic_unique gives the quadratic uniqueness. contact_lag_signs and the two
signProduct window results prove (d), and symbol_factor/Psi_one include the exact factors and
endpoint value.
-/
#check @polyak.ModeLocking.TwoLag.symbol_factor
#check @polyak.ModeLocking.TwoLag.symbol_pi_neg
#check @polyak.ModeLocking.TwoLag.double_tangencies_iff
#check @polyak.ModeLocking.TwoLag.Hermite_of_lag_tangencies
#check @polyak.ModeLocking.TwoLag.Hermite_quadratic_unique
#check @polyak.ModeLocking.TwoLag.contact_lag_signs
#check @polyak.ModeLocking.TwoLag.signProduct_window
#check @polyak.ModeLocking.TwoLag.signProduct_below
#check @polyak.ModeLocking.TwoLag.Psi_one

/-!
Article: Theorem G.15 [thm:exact313]. An exact two-lag point of $3/13$.

The concrete 3/13 tuning has the exact rational location bounds, original-system nonsingular
Jacobian/local uniqueness, E1–E4, zero thresholds and analytic plateau with the unique anchor
and spectrum.

qStar_location matches all three decimal radii as exact rationals. sourceContactSystem_zero,
source_jacobian_invertible and sourceContactSystem_locally_unique concern the original
kappa,y,beta equations. exactData supplies every E1–E4 field. exact313_extremals constructs a
regular witness with exactly the two stated frequencies and classifies every solution with the
exact zero-atom admissibility bound.
-/
#check @polyak.CertifiedExamples.Exact313.qStar_location
#check @polyak.CertifiedExamples.Exact313.sourceContactSystem_zero
#check @polyak.CertifiedExamples.Exact313.source_jacobian_invertible
#check @polyak.CertifiedExamples.Exact313.sourceContactSystem_locally_unique
#check @polyak.CertifiedExamples.Exact313.exactData
#check @polyak.CertifiedExamples.Exact313.qStar_gap
#check @polyak.CertifiedExamples.Exact313.thresholds_zero
#check @polyak.CertifiedExamples.Exact313.open_analytic_plateau
#check @polyak.CertifiedExamples.Exact313.unique_anchor
#check @polyak.ArticleResults.exact313_extremals

/-!
Article: Lemma H.1 [lem:edgeidjk]. Edge identities.

Both exact edge trigonometric identities and all four first/second derivative formulas hold at
the rational contact.

The residue-one and residue-zero identities are proved for arbitrary curve extensions.
lag_first/second_position_one_twice and position_zero_twice assume actual twice
differentiability and the trigonometric values supplied by the grid/congruence identities. They
retain the exact factors sin(cprime), cos(cprime), n and 2*Theta-prime.
-/
#check @polyak.FareyPlateau.Edge.position_one_identity
#check @polyak.FareyPlateau.Edge.position_zero_identity
#check @polyak.FareyPlateau.Edge.lag_first_position_one_twice
#check @polyak.FareyPlateau.Edge.lag_second_position_one_twice
#check @polyak.FareyPlateau.Edge.lag_first_position_zero_twice
#check @polyak.FareyPlateau.Edge.lag_second_position_zero_twice

/-!
Article: Theorem H.2 [thm:edgejk]. Edge criterion at a Farey fraction.

Nonresonance supplies the adjacent edge lags; all jets, threshold and extremal claims, regular
certificate and singleton obstruction follow.

adjacentData_nonempty derives the lower and upper lags from nonresonance. AdjacentData stores
only their location, class and mixing coordinate. Its four zero jets and two curvature
identities match (a). threshold and strict_complement_classification give (b); certificate
constructs the regular witness under its three strict conditions. obstruction and
not_regular_singleton cover every allowed finite symbol and every proposed period L in (c).
-/
#check @polyak.FareyPlateau.Edge.adjacentData_nonempty
#check @polyak.FareyPlateau.Edge.AdjacentData.value_zero
#check @polyak.FareyPlateau.Edge.AdjacentData.first
#check @polyak.FareyPlateau.Edge.AdjacentData.endpoint_zero
#check @polyak.FareyPlateau.Edge.AdjacentData.endpoint_first
#check @polyak.FareyPlateau.Edge.AdjacentData.endpoint_second
#check @polyak.FareyPlateau.Edge.AdjacentData.second
#check @polyak.FareyPlateau.Edge.AdjacentData.certificate
#check @polyak.FareyPlateau.Edge.AdjacentData.threshold
#check @polyak.FareyPlateau.Edge.AdjacentData.strict_complement_classification
#check @polyak.FareyPlateau.Edge.AdjacentData.obstruction
#check @polyak.FareyPlateau.Edge.AdjacentData.not_regular_singleton

/-!
Article: Lemma H.3 [lem:certjk]. Single-harmonic certificates.

The strict one-frequency certificate is regular and persists with the exact shift and
all-extremal two-Dirac classification.

Certificate contains precisely the finite support/classes, positive normalized weights, original
strict symbol, contact curvature and endpoint moment, plus the fixed rational frequency.
Certificate.regular constructs RegularData, and certjk_near proves the full local threshold
identity, regularity and every finite-measure extremal classification with a<=b*cos(cprime).
-/
#check @polyak.FareyPlateau.Edge.Certificate
#check @polyak.FareyPlateau.Edge.Certificate.regular
#check @polyak.FareyPlateau.Edge.Certificate.certjk_near

/-!
Article: Corollary H.4 [cor:onejk]. Single-harmonic plateaus.

A singleton-support boundary plateau lies on its exact rational tongue boundary and has the
unique stated anchor in the gap.

singleton_boundary_graph derives phase=cprime and the explicit tongue equality from actual
regular data with singleton support. singleton_kappaBoundary identifies the full condition
threshold with that tongue. singleton_plateau_anchor uses intrinsic support constancy and proves
the anchor equivalence for every measure throughout the plateau gap part.
-/
#check @polyak.FareyPlateau.Edge.singleton_boundary_graph
#check @polyak.FareyPlateau.Edge.singleton_kappaBoundary
#check @polyak.FareyPlateau.Edge.singleton_plateau_anchor

/-!
Article: Lemma H.5 [lem:Ppoly].

The displayed trigonometric polynomial is everywhere nonnegative, has exactly the two root
classes, and both roots have the stated positive second derivative.

polynomial unfolds to exactly Upsilon_k. polynomial_nonneg quantifies all real theta;
polynomial_eq_zero_iff gives precisely the two 2*pi classes. The two second-derivative
identities and their joint positivity include k=3.
-/
#check @polyak.FareyPlateau.Fan.polynomial
#check @polyak.FareyPlateau.Fan.polynomial_nonneg
#check @polyak.FareyPlateau.Fan.polynomial_eq_zero_iff
#check @polyak.FareyPlateau.Fan.polynomial_second_zero
#check @polyak.FareyPlateau.Fan.polynomial_second_other
#check @polyak.FareyPlateau.Fan.polynomial_second_roots_pos

/-!
Article: Lemma H.6 [lem:edgedomain]. The edge in the gap.

The edge tuning exists uniquely in its gap exactly above the positive convex finite maximum of
the four affine faces; the second face is redundant.

aE is the literal max of the four displayed affine functions, so piecewise affinity is
definitional. source_edgedomain proves the iff for the actual tuning with those coefficients;
source_edge_exists_unique supplies existence and uniqueness above the same bound. convexOn_aE
and aE_pos prove convexity and positivity; aE_three_faces removes exactly the second source
term.
-/
#check @polyak.FareyPlateau.aE
#check @polyak.FareyPlateau.source_edgedomain
#check @polyak.FareyPlateau.source_edge_exists_unique
#check @polyak.FareyPlateau.convexOn_aE
#check @polyak.FareyPlateau.aE_pos
#check @polyak.FareyPlateau.aE_three_faces

/-!
Article: Definition H.7 [def:admissible]. Admissible symbols.

Admissibility is finite positive support with the stated classes, gcd and slope balance; the
phase floor, removable curvature quotient, infimum and adjacent symbol are the source
definitions.

Zero weights are trimmed before enumeration; Admissible records injectivity, nonzero lags,
positive normalized weights, two residue-one lags, support gcd one and the displayed balance
equation. SourceCertificate contains ONLY this finite data. phaseFloor_data proves analyticity,
endpoint values and both contact jets; contact_value/off_contact identify R with the piecewise
source formula. aF is the infimum over every such finite support, with no lag cutoff. edgeSymbol
is built from the floor-adjacent lags using only nonresonance; edgeSymbol_contact identifies its
a2.
-/
#check @polyak.FareyPlateau.Symbols.Admissible
#check @polyak.FareyPlateau.Ray.SourceCertificate
#check @polyak.FareyPlateau.Ray.SourceCertificate.R
#check @polyak.FareyPlateau.Ray.aF
#check @polyak.FareyPlateau.Ray.SourceCertificate.contact_value
#check @polyak.FareyPlateau.Ray.SourceCertificate.off_contact
#check @polyak.FareyPlateau.Ray.SourceCertificate.phaseFloor_data
#check @polyak.FareyPlateau.Ray.edgeSymbol
#check @polyak.FareyPlateau.Ray.a2
#check @polyak.FareyPlateau.Ray.edgeSymbol_contact

/-!
Article: Lemma H.8 [lem:ray]. The certificate criterion along the edge.

The continuous edge quotient has the exact max-R certificate criterion, yields regularity, and
has the sharp adjacent-symbol curvature lower bound and formula.

analytic_R proves regularity of the actual removable quotient from admissibility. ray_criterion
is a iff of the three original strict certificate conditions and a>maximum. regular_threshold
constructs regularity. source_sharp/source_sharp_eq_iff prove the a2 bound and equality only for
the exact adjacent support weights. edgeF_curvature is the stated factor
2*sin(omega0)*sin(cprime)^3*(a-a2); edgeA2 unfolds to all four displayed terms.
source_edge_exists_unique supplies existence for all sufficiently large a.
-/
#check @polyak.FareyPlateau.Ray.SourceCertificate.analytic_R
#check @polyak.FareyPlateau.Ray.SourceCertificate.ray_criterion
#check @polyak.FareyPlateau.Ray.SourceCertificate.regular_threshold
#check @polyak.FareyPlateau.Ray.SourceCertificate.source_sharp
#check @polyak.FareyPlateau.Ray.SourceCertificate.source_sharp_eq_iff
#check @polyak.FareyPlateau.Ray.edgeF_curvature
#check @polyak.FareyPlateau.Ray.edgeA2
#check @polyak.FareyPlateau.source_edge_exists_unique

/-!
Article: Theorem H.9 [thm:largea]. Single-harmonic plateaus at large curvature.

The explicit four-term large-curvature cutoff constructs the three-lag certificate on every
bounded D strip, a boundary regular tuning and the stated finite aF upper bound.

a1 is exactly the source maximum using slopeBound, lagBound and centralFactor. SourceData
contains only tuning coefficients, fraction/inverse data and the explicit cutoff assumptions;
its n,w are the three displayed nearest-lag weights, and admissibility is proved. largea
constructs actual boundary regularity and a certificate below a; sourceCertificate_nonempty and
aF_le_upperMajorant discharge nonemptiness and prove the finite max(a1,aE) bound for every D.
-/
#check @polyak.FareyPlateau.LargeCurvature.a1
#check @polyak.FareyPlateau.LargeCurvature.largea
#check @polyak.FareyPlateau.LargeCurvature.aF_le_upperMajorant
#check @polyak.FareyPlateau.LargeCurvature.SourceData.n
#check @polyak.FareyPlateau.LargeCurvature.SourceData.w
#check @polyak.FareyPlateau.LargeCurvature.SourceData.near
#check @polyak.FareyPlateau.LargeCurvature.SourceData.admissible
#check @polyak.FareyPlateau.LargeCurvature.SourceData.certificate

/-!
Article: Corollary I.1 [cor:omega1]. A neighborhood of $\partial\Omega_1$.

At each nonlocked lag-one frontier point divergence is locally absent; near a tongue tip it is
exactly the closed tongue, and every gap-boundary closure avoids that frontier.

Both declarations retain the phase-locking hypotheses. omega_one_nonlocked uses the proved
strict positive threshold of a nonlocked frontier point. omega_one_tip extracts an actual open
neighborhood from the proved tip persistence theorem; Tip contains only period>=3, frontier
membership and the phase-contact equation. closure_gap_boundary_disjoint_omegaOne gives the
final closure statement for every K.
-/
#check @polyak.ArticleResults.omega_one_nonlocked
#check @polyak.ArticleResults.omega_one_tip
#check @polyak.GapEdges.closure_gap_boundary_disjoint_omegaOne

/-!
Article: Proposition I.2 [prop:corner]. Junctions.

The actual adjacent symbol has the source junction curvature formula; its negative-curvature
interval is nonempty, nonresonant and yields a full neighborhood inside divergence.

junction_firstChi identifies chi with the original tuning derivative and
-a*(t1-t2)*sin(cprime)^2. The small formula combined with junction_curvature_source_form is
exactly the displayed factorization, with k=K+1; junction_interval_g_bounds proves |chi|<k/2.
first_adjacent_exists discharges nonresonance. junction_adjacent_negative_iff covers every
nonresonant lag cell. The final three Consequence theorems construct the actual q_cross and its
negative threshold/interior neighborhood.
-/
#check @polyak.GapEdges.Junction.junction_firstChi
#check @polyak.GapEdges.Junction.first_adjacent_exists
#check @polyak.GapEdges.Junction.junction_adjacent_small_formula
#check @polyak.GapEdges.Junction.junction_adjacent_negative_iff
#check @polyak.GapEdges.Junction.junction_curvature_source_form
#check @polyak.GapEdges.Junction.junction_interval_g_bounds
#check @polyak.GapEdges.Junction.source_junction_interval_nonempty
#check @polyak.GapEdges.Junction.junctionTuning_sigma_negative
#check @polyak.GapEdges.Junction.junctionTuning_interior_neighborhood

/-!
Article: Lemma I.3 [lem:junction]. The curve at a junction.

The generic arccotangent junction profile has exactly the displayed value and first and second
derivatives.

generic_junction_angle_jets quantifies arbitrary real a,t2 and any half-angle c in (0,pi/2),
hence specializes to every integer m>=4 and the stronger source a>0,t2<t1 hypotheses. It works
directly for the arccotangent profile with arbitrary coefficients in this domain.
-/
#check @polyak.GapEdges.Junction.generic_junction_angle_jets

/-!
Article: Lemma I.4 [lem:cornerineq].

The exact trigonometric corner inequality holds for every integer m≥4.

corner_inequality uses junctionU and junctionT defined by the actual sine/cosine formulas, and
quantifies every natural m>=4. Its proof handles m=4,5 exactly and proves the remaining tail
analytically; no sampled m cutoff or empirical verification is used.
-/
#check @polyak.GapEdges.Junction.corner_inequality
