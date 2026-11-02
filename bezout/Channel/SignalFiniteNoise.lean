import bezout.Channel.SignalBounds
import bezout.Channel.FiniteNoiseRemainder

/-!
Article: bezout, Equations `eq:experiment-T` and `eq:experiment-finite-variance`.
Use: the singleton coefficients of the full physical random channel are exactly
T's columns; the exact variance is delta^2 times its HS energy plus a nonnegative
fixed-horizon fourth-order remainder.
Proof: the actual singleton-response theorem in diagonal spectral coordinates,
finite Parseval identity and the explicit nonnegative higher-mask sum.
-/

namespace bezout.Channel
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- A singleton finite-noise coefficient is exactly the corresponding actual T column. -/
theorem finiteNoiseCoefficient_signal_column (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (s : Fin N) (j : J) :
    finiteNoiseCoefficient h (bezout.History.matrixEnd (Matrix.diagonal lam))
      (fun _ => LinearMap.id) a {s.val} j=signalMatrix h lam a.ofLp j s := by
  rw [finiteNoiseCoefficient_singleton]
  simp only [LinearMap.id_apply, diagonal_polynomial_apply, signalMatrix, bezout.Lower.physicalKernel]
  ring

/-- Sum of the actual singleton coefficient energies is exactly the squared HS signal norm. -/
theorem finiteNoiseCoefficient_signal_energy (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) :
    (∑ s : Fin N, ‖finiteNoiseCoefficient h (bezout.History.matrixEnd (Matrix.diagonal lam))
      (fun _ => LinearMap.id) a {s.val}‖^2)=rectangularHsSq (signalMatrix h lam a.ofLp) := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, finiteNoiseCoefficient_signal_column]
  exact Finset.sum_comm

/-- The full finite random channel has the exact leading HS variance and its actual remainder. -/
theorem finiteSignOutput_signal_variance (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (δ : ℝ) :
    (∫ ω, ‖finiteSignOutput h (bezout.History.matrixEnd (Matrix.diagonal lam))
      (fun _ => LinearMap.id) a δ ω-
        (aeval (bezout.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a‖^2
          ∂bezout.Probability.Signs.law N)=
      δ^2*rectangularHsSq (signalMatrix h lam a.ofLp)+
        finiteNoiseRemainder h (bezout.History.matrixEnd (Matrix.diagonal lam))
          (fun _ => LinearMap.id) a δ := by
  rw [finiteSignOutput_variance_split, finiteNoiseCoefficient_signal_energy]

end
end bezout.Channel
