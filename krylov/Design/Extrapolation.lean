import krylov.Design.DegenerateWeights
import krylov.Design.OptimalLimits
import krylov.Design.EllipticNome
import krylov.Design.FCDesignBridge

/-!
Article: main_krylov, stage 8: thm:B, lem:chebyshev-design,
apC:lem:natoms and apC:lem:poisson, including the Chebyshev majorants.

This final import leaf assembles the full original extrapolation-design scope:
actual all-measure optimization with singular and zero-weight cases; sharp
support bounds; true directional derivatives and sensitivity certificates;
positive physical Lobatto designs and prescribed-atom suprema; the exact
actual-FC coefficient/design supremum bridge and uniform-budget identity; finite and
infinite majorants and their genuine limits; both actual Poisson formulas,
positive exponential remainders, and the true elliptic integral/nome identity.

The M+1 support reduction is proved by sensitivity-polynomial multiplicities,
rather than by separately constructing a Gaussian rule for arbitrary inputs.
The elliptic reformulation is proved by actual convergent lattice convolutions,
Lambert-series rearrangement, AGM iteration and the original Landen integral.
No optimizer, quadrature reduction, Fourier formula or theta identity is
assumed as a certificate field.
-/
