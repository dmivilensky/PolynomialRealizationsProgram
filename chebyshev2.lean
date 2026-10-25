import chebyshev2.DualCertificate.ArticleTransfer
import chebyshev2.Calibration.SelfConsistency
import chebyshev2.Certificates.Compact.ReferenceBase
import chebyshev2.Comparison.RightJost
import chebyshev2.Comparison.RightRepresentation
import chebyshev2.Comparison.SymmetricTranslation
import chebyshev2.DualCertificate.NormalizedStateSmooth
import chebyshev2.DualCertificate.NumericalIntegrands
import chebyshev2.Filters.Linearization
import chebyshev2.Finite.OptimalSymmetric
import chebyshev2.Green.CenteringEquivalence
import chebyshev2.HalfLine.Profiles
import chebyshev2.LocalObstruction.Article
import chebyshev2.LocalObstruction.FullGreenVariation
import chebyshev2.LocalObstruction.ObservationNeighborhood
import chebyshev2.Numerics.CubicNewton
import chebyshev2.Numerics.CubicQuotientCheck
import chebyshev2.Numerics.PolynomialTranslation
import chebyshev2.Numerics.StateBoxRules
import chebyshev2.Numerics.StateIntervalJet
import chebyshev2.Primal.Feasibility
import chebyshev2.SineContinuum.EnergyFiniteSum
import chebyshev2.SineContinuum.MercerUniform
import chebyshev2.SineContinuum.StandardRealization
import chebyshev2.SineJacobi.UniformDiagonal
import chebyshev2.StateRegion.BoundaryRigidity



/-!
Article: chebyshev2 — public mathematical library.
Use: `Article` presents its article statements; `Check` verifies all sources and their trust boundary.
Imports cover the complete analytic library and the numerical conclusions in README.
-/
