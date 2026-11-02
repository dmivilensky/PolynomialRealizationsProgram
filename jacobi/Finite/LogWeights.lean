import jacobi.Finite.ReversalWeights
import jacobi.Finite.AnalyticGram
import Mathlib.Analysis.Analytic.Constructions

/-!
Article: jacobi, Proposition 1.1.
The logarithmic inverse chart is defined on the full real coordinate space.
Common additive shifts are redundant; the exact inverse and shift identities
express the quotient by constants without choosing a manifold implementation.
Source: elementary exponential/logarithm calculus and the finite spectral chart.
Use: normalizes the analytic positive weights of the entire finite fibre.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Real InnerProductSpace
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (S : Nodes (n+1))

/-- The partition sum in logarithmic spectral coordinates.
Use: normalizes the analytic positive weights of the entire finite fibre.
Article: jacobi, Proposition 1.1.
-/
def logNormalizer (ell : Fin (n+1) → ℝ) : ℝ :=
  ∑ k, Real.exp (ell k) * |S.polynomial.derivative.eval (S.value k)|⁻¹

/-- The logarithmic partition sum never vanishes.
Use: justifies analytic division and the inverse chart globally.
Article: jacobi, Proposition 1.1.
Proof: Every term is positive and the finite support is nonempty. -/
theorem logNormalizer_pos (ell : Fin (n+1) → ℝ) : 0 < logNormalizer S ell := by
  apply Finset.sum_pos
  · intro k _
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (abs_pos.mpr (S.derivative_ne_zero k)))
  · exact Finset.univ_nonempty

/-- The actual probability vector represented by logarithmic coordinates.
Use: reconstructs J(ell), with no unresolved probability assumptions.
Article: jacobi, Proposition 1.1.
-/
def logWeights (ell : Fin (n+1) → ℝ) : WeightSimplex (n+1) := by
  refine ⟨fun k => Real.exp (ell k) * |S.polynomial.derivative.eval (S.value k)|⁻¹ /
    logNormalizer S ell, ?_, ?_⟩
  · intro k
    exact div_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr
      (abs_pos.mpr (S.derivative_ne_zero k)))) (logNormalizer_pos S ell)
  · rw [← Finset.sum_div]
    exact div_self (logNormalizer_pos S ell).ne'

/-- Logarithmic coordinates of a positive spectral probability vector.
Use: verifies surjectivity of the logarithmic parametrization.
Article: jacobi, Proposition 1.1.
-/
def weightLogs (w : WeightSimplex (n+1)) (k : Fin (n+1)) : ℝ :=
  Real.log (w.val k * |S.polynomial.derivative.eval (S.value k)|)

/-- Logarithms followed by normalized exponentials recover the actual probabilities.
Use: every fibre element occurs in the logarithmic chart.
Article: jacobi, Proposition 1.1.
Proof: exponentiating gives w_k |p′|; cancellation makes the partition sum one. -/
theorem logWeights_weightLogs (w : WeightSimplex (n+1)) :
    logWeights S (weightLogs S w) = w := by
  -- Exponentiation cancels the characteristic-derivative factor, and the remaining weights sum to one.
  have he (k : Fin (n+1)) : Real.exp (weightLogs S w k) *
      |S.polynomial.derivative.eval (S.value k)|⁻¹ = w.val k := by
    rw [weightLogs, Real.exp_log (mul_pos (w.property.1 k)
      (abs_pos.mpr (S.derivative_ne_zero k)))]
    exact mul_inv_cancel_right₀ (abs_pos.mpr (S.derivative_ne_zero k)).ne' _
  have hz : logNormalizer S (weightLogs S w) = 1 := by
    simp only [logNormalizer, he]
    exact w.property.2
  apply Subtype.ext
  funext k
  change Real.exp (weightLogs S w k) * _ / _ = _
  rw [he, hz, div_one]

/-- Taking logarithms recovers the parameter up to its common normalization constant.
Use: identifies exactly the quotient by constants in the article.
Article: jacobi, Proposition 1.1.
Proof: multiply by |p′|, cancel its nonzero factor and take the logarithm. -/
theorem weightLogs_logWeights (ell : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    weightLogs S (logWeights S ell) k = ell k - Real.log (logNormalizer S ell) := by
  have hd := abs_pos.mpr (S.derivative_ne_zero k)
  have he : (logWeights S ell).val k * |S.polynomial.derivative.eval (S.value k)| =
      Real.exp (ell k) / logNormalizer S ell := by
    change (_ * _⁻¹ / _) * _ = _
    field_simp
  rw [weightLogs, he, Real.log_div (Real.exp_pos _).ne' (logNormalizer_pos S ell).ne',
    Real.log_exp]

/-- Adding a common constant changes no probability and hence no reconstructed matrix.
Use: the inverse chart is genuinely defined on the article's quotient coordinates.
Article: jacobi, Proposition 1.1.
Proof: the common positive exponential factor cancels from the partition sum. -/
theorem logWeights_shift (ell : Fin (n+1) → ℝ) (c : ℝ) :
    logWeights S (fun k => ell k + c) = logWeights S ell := by
  -- The common exponential factor cancels between every numerator and the partition sum.
  have hz : logNormalizer S (fun k => ell k+c) = Real.exp c * logNormalizer S ell := by
    simp only [logNormalizer, Real.exp_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply Subtype.ext
  funext k
  change Real.exp (ell k+c) * _ / _ = Real.exp (ell k) * _ / logNormalizer S ell
  rw [Real.exp_add, hz]
  field_simp

/-- Zero logarithmic coordinates represent exactly the canonical persymmetric weights.
Use: identifies the critical point in the constructed coordinate system.
Article: jacobi, Proposition 1.1.
Proof: At zero every exponential is one, giving precisely the reciprocal-derivative normalization. -/
theorem logWeights_zero : logWeights S 0 = S.persymmetricWeights := by
  apply Subtype.ext
  funext k
  simp [logWeights, logNormalizer, Nodes.persymmetricWeights, Nodes.derivativeNormalizer]

/-- The actual fibre element in logarithmic spectral coordinates.
Use: the real-analytic energy below is the existing Jacobi energy, not a surrogate.
Article: jacobi, Proposition 1.1.
-/
def logFiber (ell : Fin (n+1) → ℝ) : Fiber (n+1) S.polynomial :=
  reconstructFiber S (logWeights S ell)

/-- Each coordinate of the open-simplex probability vector is globally real-analytic.
Use: proves analytic dependence of the Gram input and reconstructed Jacobi matrix.
Article: jacobi, Proposition 1.1.
Proof: analytic exponentials, finite sums and a strictly positive denominator. -/
theorem logWeights_analytic (ell : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    AnalyticAt ℝ (fun v => (logWeights S v).val k) ell := by
  -- Coordinate projections are continuous linear maps; the normalization denominator is positive everywhere.
  have he (j : Fin (n+1)) : AnalyticAt ℝ
      (fun v : Fin (n+1) → ℝ => Real.exp (v j) *
        |S.polynomial.derivative.eval (S.value j)|⁻¹) ell :=
    by
      have hj : AnalyticAt ℝ (fun v : Fin (n+1) → ℝ => v j) ell :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) j).analyticAt ell
      exact ((AnalyticGram.exp_analytic (ell j)).comp (f := fun v : Fin (n+1) → ℝ => v j) hj).mul
        analyticAt_const
  have hz : AnalyticAt ℝ (logNormalizer S) ell :=
    Finset.analyticAt_fun_sum _ (fun j _ => he j)
  exact (he k).div hz (logNormalizer_pos S ell).ne'

end
end jacobi.Finite
