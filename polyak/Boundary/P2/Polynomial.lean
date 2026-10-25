import polyak.Boundary.P2.Dual
import Mathlib.Order.Interval.Set.Infinite

/-! Article: the double-square identity holds as an actual polynomial identity, with double roots. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral Polynomial

/-- Article: the independent atom polynomial, before selecting its real roots. -/
def atomPoly (z : ℝ) : ℝ[X] := X^2+C (atomA z)*X+C (atomB z)

/-- Article: its semantic evaluation is exactly the source atom equation. -/
theorem atomPoly_eval (z c : ℝ) : (atomPoly z).eval c=atomPolynomial z c := by
  simp [atomPoly,atomPolynomial]

/-- Article: the actual dual polynomial is precisely the stated scalar times a double square. -/
theorem dualPolynomial_eq {z : ℝ} (hz : z∈parameterInterval) :
    dualPolynomial (dualWeights z hz) (u z) (G z)=
      C (4*(1-W z)/(4*G z^2-1))*(atomPoly z)^2 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Icc_infinite (show (-1 : ℝ)<1 by norm_num)).mono
  intro c hc
  change (dualPolynomial (dualWeights z hz) (u z) (G z)).eval c=
    (C (4*(1-W z)/(4*G z^2-1))*(atomPoly z)^2).eval c
  have h:=dualPolynomial_factor_p2 hz (⟨c,hc⟩ : Frequency)
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,atomPoly_eval] using h

/-- Article: each selected support root is stationary for the actual dual polynomial. -/
theorem dualPolynomial_stationary {z : ℝ} (hz : z∈parameterInterval) {c : ℝ}
    (hc : c=x z ∨ c=y z) :
    (dualPolynomial (dualWeights z hz) (u z) (G z)).derivative.eval c=0 := by
  have hr : (atomPoly z).eval c=0 := by
    rw [atomPoly_eval]
    rcases hc with rfl|rfl
    · exact atomPolynomial_x hz
    · exact atomPolynomial_y hz
  rw [dualPolynomial_eq hz]
  simp [Polynomial.derivative_pow,hr]

end
end polyak.Boundary.P2
