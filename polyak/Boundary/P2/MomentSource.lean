import polyak.Boundary.P2.Source

/-!
Article: reduction of every lag polynomial modulo the monic atom quadratic.
Use: one specified linear moment functional defines the rational raw slacks.
Its equality with actual probability integrals is proved in Moments.lean.
-/

namespace polyak.Boundary.P2
noncomputable section
open Polynomial Spectral

/-- Article: the source linear moment functional on actual real polynomials. -/
def momentLinear (z : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => LinearMap.mulRight ℝ (moment z n))

/-- Article: source reduction preserves the prescribed power moment. -/
theorem momentLinear_monomial (z : ℝ) (n : ℕ) (a : ℝ) :
    momentLinear z (monomial n a)=a*moment z n := by
  simp [momentLinear,Polynomial.lsum,Polynomial.sum_monomial_index]

/-- Article: coefficient-times-power form of the source moment identity. -/
theorem momentLinear_C_mul_X_pow (z : ℝ) (a : ℝ) (n : ℕ) :
    momentLinear z (C a*X^n)=a*moment z n := by
  rw [C_mul_X_pow_eq_monomial,momentLinear_monomial]

/-- Article: the actual raw upper/lower rational source after quadratic reduction.
The sign δ=−1 selects the lower slack; δ=1 selects the upper slack. -/
def reducedSlack (z : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  momentLinear z ((1-X^2-C (u z^2))*(C (chebT n (G z))-Chebyshev.T ℝ (n : ℤ))+
    C (δ*2*u z)*(1-X^2)*Chebyshev.U ℝ ((n-1 : ℕ) : ℤ))-
    δ*d z*chebU (n-1) (G z)

end
end polyak.Boundary.P2
