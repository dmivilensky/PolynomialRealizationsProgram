import jacobi.Jacobi.Degree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Article: jacobi, Lemma C.1.
The genuine finite Jacobi polynomial is composed with cos(theta). Both
actual ordinary derivatives and the exact angular Sturm equation are
proved before introducing the singular Liouville weight.
Use: its positive Liouville multiple has exactly the source's n angular zeros.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Jacobi function at the angular coordinate cos(theta).
Use: its positive Liouville multiple has exactly the source's n angular zeros.
Article: jacobi, Proposition B.1.
-/
def angular (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (shiftedPolynomial a b n).eval ((1-cos t)/2)

/-- The explicit actual first angular Jacobi derivative.
Use: supplies the ordinary derivative in the Liouville transformation.
Article: jacobi, Proposition B.1.
-/
def angularSlope (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  sin t/2*(shiftedPolynomial a b n).derivative.eval ((1-cos t)/2)

/-- The explicit actual second angular Jacobi derivative.
Use: converts the literal polynomial Jacobi equation into the angular restoring equation.
Article: jacobi, Lemma C.1.
-/
def angularAcceleration (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  cos t/2*(shiftedPolynomial a b n).derivative.eval ((1-cos t)/2)+
    sin t^2/4*(shiftedPolynomial a b n).derivative.derivative.eval ((1-cos t)/2)

/-- The angular function is the original real normalized Jacobi function at cos(theta).
Use: the Liouville function retains the actual source polynomial and its zero set.
Article: jacobi, Proposition B.1.
Proof: use the previously proved exact affine shifted-polynomial identity. -/
theorem angular_eq_realNormalized (a b : ℝ) (n : ℕ) (t : ℝ) :
    angular a b n t=realNormalized a b n (cos t) := by
  rw [angular,shiftedPolynomial_eval]
  congr 1
  ring

/-- The explicit angular slope is the true ordinary derivative everywhere.
Use: the subsequent wave equation concerns actual derivatives of the actual finite polynomial.
Article: jacobi, Proposition B.1.
Proof: apply the community polynomial derivative and the cosine chain rule. -/
theorem angular_hasDerivAt (a b : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (angular a b n) (angularSlope a b n t) t := by
  have hc := ((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).div_const 2
  convert ((shiftedPolynomial a b n).hasDerivAt ((1-cos t)/2)).comp t hc using 1
  · rfl
  · dsimp [angularSlope]
    ring

/-- The explicit angular acceleration is the true derivative of the angular slope.
Use: provides both genuine derivatives required by the source's second-order Liouville equation.
Article: jacobi, Proposition B.1.
Proof: apply the product rule and the same actual polynomial chain rule to the first derivative. -/
theorem angularSlope_hasDerivAt (a b : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (angularSlope a b n) (angularAcceleration a b n t) t := by
  have hc := ((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).div_const 2
  have hp := ((shiftedPolynomial a b n).derivative.hasDerivAt ((1-cos t)/2)).comp t hc
  convert ((Real.hasDerivAt_sin t).div_const 2).mul hp using 1
  · rfl
  · dsimp [angularAcceleration]
    ring

/-- The genuine angular Jacobi function satisfies its exact angular Sturm equation on the open angle interval.
Use: removes the first derivative by the source's positive singular Liouville weight.
Article: jacobi, Proposition B.1.
Proof: substitute t=(1-cos(theta))/2 into the actual shifted polynomial
equation. The sine-square identity gives the leading coefficient; positivity
of sin(theta) justifies cancellation in the first-derivative coefficient. -/
theorem angular_equation {a b : ℝ} (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    angularAcceleration a b n t+((a-b)+(a+b+1)*cos t)/sin t*angularSlope a b n t+
      (n:ℝ)*(n+a+b+1)*angular a b n t=0 := by
  -- This equation is proved from the actual polynomial equation, including its finite degree and parameters.
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have h := shiftedPolynomial_equation_eval (b := b) ha n ((1-cos t)/2)
  dsimp only at h
  unfold angularAcceleration angularSlope angular
  rw [show ((a-b)+(a+b+1)*cos t)/sin t*(sin t/2*
    (shiftedPolynomial a b n).derivative.eval ((1-cos t)/2))=
      ((a-b)+(a+b+1)*cos t)/2*(shiftedPolynomial a b n).derivative.eval ((1-cos t)/2) by
        field_simp [hs.ne']]
  linear_combination h+((shiftedPolynomial a b n).derivative.derivative.eval ((1-cos t)/2)/4)*
    Real.sin_sq_add_cos_sq t

end
end jacobi.Jacobi
