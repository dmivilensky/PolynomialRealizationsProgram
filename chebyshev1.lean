/- Public entry points; their imports cover every mathematical module in chebyshev1. -/
import chebyshev1.Background.FiniteFavard
import chebyshev1.Background.GraphSpectrum
import chebyshev1.Background.HeavyBallLimit
import chebyshev1.Background.HeavyBallOptimality
import chebyshev1.Background.Minimax
import chebyshev1.Background.NumericalComparisons
import chebyshev1.Background.PrefixWeights
import chebyshev1.Background.RecordedCG
import chebyshev1.Background.Schur
import chebyshev1.Background.SignedEndpoint
import chebyshev1.Background.StepsizeClassification
import chebyshev1.Chebyshev.AccuracyScale
import chebyshev1.Chebyshev.AmplificationCertificates
import chebyshev1.Chebyshev.ExactAccuracyScale
import chebyshev1.Chebyshev.ExpandedMaximum
import chebyshev1.Jacobi.EndpointComparison
import chebyshev1.Jacobi.FiniteClassification
import chebyshev1.Jacobi.NormalizedWords
import chebyshev1.Jacobi.OperatorL2
import chebyshev1.Nonlinear.LipschitzHessian
import chebyshev1.Nonlinear.LeadingMaximum
import chebyshev1.Nonlinear.ObjectiveModels
import chebyshev1.Nonlinear.ObjectiveLocalLipschitz
import chebyshev1.Nonlinear.PrefixMonotonicity
import chebyshev1.Nonlinear.PrefixSecondOrderLimit
import chebyshev1.Nonlinear.Restart
import chebyshev1.Nonlinear.Translation
import chebyshev1.Perturbations.SmoothExpansion
import chebyshev1.Perturbations.ThirdDerivative
import chebyshev1.Prefix.FirstStep
import chebyshev1.Prefix.RatioAlgorithm
import chebyshev1.Realization.Normalization
import chebyshev1.Realization.AffineMethods
import chebyshev1.Realization.Minimax
import chebyshev1.Realization.UniversalGain
import chebyshev1.SineJacobi.Algorithm
import chebyshev1.SineJacobi.Comparison
import chebyshev1.SineJacobi.EndpointAsymptotics
import chebyshev1.SineJacobi.EnergyDecimal
import chebyshev1.SineJacobi.FirstGreenAsymptotics
import chebyshev1.SineJacobi.Orthogonality
import chebyshev1.SineJacobi.ProfileUniqueness
import chebyshev1.SineJacobi.Resolvent
import chebyshev1.SineJacobi.RatioAlgorithm
import chebyshev1.SineJacobi.ReversalWeights
import chebyshev1.Spectral.Sharpness
import chebyshev1.Stepsize.LowerBound
import chebyshev1.Stepsize.PrefixAsymptotics
import chebyshev1.Stepsize.EndpointProfile
import chebyshev1.Stochastic.FiniteGossip
import chebyshev1.Stochastic.FiniteIndependentSpectral
import chebyshev1.Stochastic.FiniteMatrixRun
import chebyshev1.Stochastic.FiniteScalarNoise
import chebyshev1.Stochastic.GossipConditional
import chebyshev1.Stochastic.GossipAsymptotics
import chebyshev1.Stochastic.GossipScaling
import chebyshev1.Stochastic.GossipFrame
import chebyshev1.Stochastic.GraphFrame
import chebyshev1.Stochastic.QuadraticCovariance
import chebyshev1.Stochastic.QuadraticCovarianceBounds
import chebyshev1.Stochastic.MatrixQuadraticCovariance
import chebyshev1.Stochastic.MatrixMoments
import chebyshev1.Stochastic.ScalarNoise
import chebyshev1.Stochastic.SphereCurvatureRun
import chebyshev1.Stochastic.VolterraBound
import chebyshev1.TwoTerm.Optimality

/-!
Article: chebyshev1 — public mathematical library.
Use: `Article` presents its article statements; `Check` verifies all sources and their trust boundary.
Imports cover the complete analytic library and the numerical conclusions in README.
-/
