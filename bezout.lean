import bezout.Algorithms.BalancedCached
import bezout.Algorithms.FlatScalarCost
import bezout.Algorithms.Translation
import bezout.Balanced.AuxiliaryRecurrence
import bezout.Balanced.Optima
import bezout.Channel.Roots.Signal
import bezout.Channel.SignalAdditiveSpectral
import bezout.Channel.SignalFiniteNoise
import bezout.Channel.SignalVarianceSeparation
import bezout.Comparisons.Classical.VarianceLimit
import bezout.Comparisons.Competitors.DFBHistory
import bezout.Comparisons.Competitors.DFBVariance
import bezout.Comparisons.Competitors.LF
import bezout.Comparisons.Competitors.MASG
import bezout.Gains.MatrixOperator
import bezout.Gains.RelativeSupremum
import bezout.Models.CycleChannel
import bezout.Probability.DitherHistory
import bezout.Properties.Minimax
import bezout.Risk.Suprema

/-!
Public mathematical library for the complete symbolic results of bezout:
Chebyshev-exact histories, attained Flat/Balanced optima, actual physical
algorithms, competitor and finite-noise comparisons, and the general ridge
and network models. Only granular analytic imports are retained, without
numerical proof archives or experiment generators. Use bezout.Article for
ordered mathematical signatures and bezout.Check for complete source and
transitive-axiom verification.
-/
