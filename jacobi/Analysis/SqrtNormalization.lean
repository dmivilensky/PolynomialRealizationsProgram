import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: jacobi, Proposition C.3.
Elementary positive square-root normalizations used to pass from the
actual polynomial edge limit to the signed, unit finite eigenvector.
Source: the positive real power and square-root laws in mathlib.
Use: target_eigenvector_degree_limit turns the separately proved actual weight and polynomial limits into the original signed eigenvector limit.
-/
namespace jacobi.Analysis
noncomputable section
open Real

/-- The degree powers in an actual positive spectral weight and its
polynomial cancel exactly, retaining the positive square-root branch.
Use: target_eigenvector_degree_limit turns the separately proved actual
weight and polynomial limits into the original signed eigenvector limit.
Article: jacobi, Proposition C.3.
Proof: combine the positive-base real powers; their exponent is 1/2. -/
theorem sqrt_weight_power {x:ℝ} (hx:0<x) (g w:ℝ) :
    sqrt (x^(1+2*g)*w)*x^(-g)=sqrt x*sqrt w := by
  rw [sqrt_mul (rpow_nonneg hx.le _),sqrt_eq_rpow (x^(1+2*g)),← rpow_mul hx.le]
  calc
    (x^((1+2*g)*(1/2))*sqrt w)*x^(-g)=
        (x^((1+2*g)*(1/2))*x^(-g))*sqrt w := by ring
    _=sqrt x*sqrt w := by
      rw [← rpow_add hx,show (1+2*g)*(1/2)+(-g)=1/2 by ring,← sqrt_eq_rpow]

/-- The original positive amplitude cancels its square in a norming
weight without changing the signed polynomial limit.
Use: target_eigenvector_degree_limit identifies the resulting scale
with the genuine positive targetWaveScale of Proposition C.2.
Article: jacobi, Proposition C.3.
Proof: the positive square root of A squared is A. -/
theorem sqrt_amplitude_cancel {A T:ℝ} (hA:0<A) (hT:0≤T) :
    sqrt (T/A^2)*A=sqrt T := by
  rw [sqrt_div hT,sqrt_sq hA.le,div_mul_cancel₀ _ hA.ne']

/-- Switching from degree normalization to true matrix-size normalization
has the exact positive square-root ratio prescribed by the article.
Use: target_eigenvector_half_limit transfers the signed degree limit
to the actual physical dimension N=n+1.
Article: jacobi, Proposition C.3.
Proof: combine the genuine nonnegative square roots and cancel n. -/
theorem sqrt_ratio_mul {N n:ℝ} (hN:0≤N) (hn:0<n) :
    sqrt (N/n)*sqrt n=sqrt N := by
  rw [← sqrt_mul (div_nonneg hN hn.le),div_mul_cancel₀ _ hn.ne']

end
end jacobi.Analysis
