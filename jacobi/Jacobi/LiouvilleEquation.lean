import jacobi.Jacobi.LiouvilleWeight

/-!
Article: jacobi, Proposition B.1.
The original finite Jacobi function times the actual positive singular
half-angle weight satisfies precisely the printed Schrodinger equation.
Both ordinary derivatives are constructed from the original functions.
Use: fixes the scaling parameter in all both-edge angular zero estimates.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The source's exact Jacobi oscillation frequency.
Use: fixes the scaling parameter in all both-edge angular zero estimates.
Article: jacobi, Proposition B.1.
-/
def frequency (a b : ℝ) (n : ℕ) : ℝ := n+(a+b+1)/2

/-- The source's endpoint inverse-square correction.
Use: the exact singular restoring coefficient and the Bessel reference use the same endpoint parameter.
Article: jacobi, Proposition B.1.
-/
def endpointCorrection (a : ℝ) : ℝ := 1/4-a^2

/-- The actual normalized Jacobi Liouville wave.
Use: transfers the true polynomial zeros into the source's restoring equation with its exact singular potential.
Article: jacobi, Proposition B.1.
-/
def liouville (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ := liouvilleWeight a b t*angular a b n t

/-- The explicit actual first derivative of the Jacobi Liouville wave.
Use: provides the first state coordinate in the source's oscillation and variation-of-constants argument.
Article: jacobi, Proposition B.1.
-/
def liouvilleSlope (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  liouvilleWeight a b t*(angularSlope a b n t+liouvilleLogSlope a b t*angular a b n t)

/-- The explicit actual second derivative of the Jacobi Liouville wave.
Use: proves the precise singular Schrodinger equation by substituting the genuine angular equation.
Article: jacobi, Proposition B.1.
-/
def liouvilleAcceleration (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  liouvilleWeight a b t*(angularAcceleration a b n t+2*liouvilleLogSlope a b t*angularSlope a b n t+
    (liouvilleLogAcceleration a b t+liouvilleLogSlope a b t^2)*angular a b n t)

/-- The explicit Liouville slope is the true ordinary derivative of the original weighted Jacobi function.
Use: establishes genuine, rather than formal, state derivatives for the later zero comparison.
Article: jacobi, Proposition B.1.
Proof: differentiate the actual positive weight and actual angular function, and collect the logarithmic slope factor. -/
theorem liouville_hasDerivAt (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    HasDerivAt (liouville a b n) (liouvilleSlope a b n t) t := by
  convert (liouvilleWeight_hasDerivAt a b ht).mul (angular_hasDerivAt a b n t) using 1
  · rfl
  · dsimp [liouvilleSlope]
    ring

/-- The explicit Liouville acceleration is the true derivative of its actual slope.
Use: the transformed finite Jacobi wave is a genuine classical second-order solution on the full open angle interval.
Article: jacobi, Proposition B.1.
Proof: the logarithmic slope, weight and both angular derivatives already
have true ordinary derivative theorems. Apply the product rule to the actual
first derivative and collect its three second-order contributions. -/
theorem liouvilleSlope_hasDerivAt (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    HasDerivAt (liouvilleSlope a b n) (liouvilleAcceleration a b n t) t := by
  have hinner := (angularSlope_hasDerivAt a b n t).add
    ((liouvilleLogSlope_hasDerivAt a b ht).mul (angular_hasDerivAt a b n t))
  convert (liouvilleWeight_hasDerivAt a b ht).mul hinner using 1
  · rfl
  · dsimp [liouvilleAcceleration]
    ring

/-- The logarithmic Liouville slope cancels exactly half of the angular first-derivative coefficient.
Use: removes that coefficient from the actual weighted equation, uniformly for all admissible parameters.
Article: jacobi, Proposition B.1.
Proof: the double-angle identities and nonzero positive half-angle bases
reduce the cancellation to the sine-square identity and ordinary field algebra. -/
theorem liouville_first_coefficient (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    2*liouvilleLogSlope a b t=((a-b)+(a+b+1)*cos t)/sin t := by
  obtain ⟨hs,hc⟩ := half_angle_positive ht
  have ht2 : t=t/2+t/2 := by ring
  rw [liouvilleLogSlope,ht2,Real.sin_add,Real.cos_add]
  rw [show (t/2+t/2)/2=t/2 by ring]
  have he := Real.sin_sq_add_cos_sq (t/2)
  field_simp [hs.ne',hc.ne']
  linear_combination 2*(a-b)*he

/-- The actual squared frequency and endpoint corrections equal the exact transformed Jacobi potential.
Use: identifies the restoring coefficient of the genuine weighted wave with the source's printed singular Schrodinger potential.
Article: jacobi, Proposition B.1.
Proof: expand the logarithmic slope and its actual derivative. Cancelling
the positive half-angle denominators leaves a polynomial multiple of
sin^2(theta/2)+cos^2(theta/2)-1. -/
theorem liouville_potential (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    (n:ℝ)*((n:ℝ)+a+b+1)-liouvilleLogAcceleration a b t-liouvilleLogSlope a b t^2=
      frequency a b n^2+endpointCorrection a/(4*sin (t/2)^2)+endpointCorrection b/(4*cos (t/2)^2) := by
  -- The coefficient calculation is exact and imposes no endpoint-exponent sign restriction.
  obtain ⟨hs,hc⟩ := half_angle_positive ht
  unfold liouvilleLogAcceleration liouvilleLogSlope frequency endpointCorrection
  field_simp [hs.ne',hc.ne']
  linear_combination -16*((2*a+1)^2*cos (t/2)^2+(2*b+1)^2*sin (t/2)^2)*
    Real.sin_sq_add_cos_sq (t/2)

/-- The original finite Jacobi Liouville wave satisfies precisely the source's singular Schrodinger equation.
Use: supplies the unconditional analytic equation underlying the full uniform both-edge zero estimates.
Article: jacobi, Proposition B.1.
Proof: substitute the actual angular equation into the actual second
weighted derivative. The preceding exact logarithmic coefficient and
potential identities cancel the remaining first and zeroth terms. -/
theorem liouville_equation {a b : ℝ} (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    liouvilleAcceleration a b n t+
      (frequency a b n^2+endpointCorrection a/(4*sin (t/2)^2)+endpointCorrection b/(4*cos (t/2)^2))*
        liouville a b n t=0 := by
  -- Every derivative and every coefficient here belongs to the actual original finite Jacobi function.
  rw [← liouville_potential a b n ht]
  unfold liouvilleAcceleration liouville
  have h := angular_equation (b := b) ha n ht
  rw [← liouville_first_coefficient a b ht] at h
  linear_combination liouvilleWeight a b t*h

/-- The genuine weighted wave has exactly the zeros of the actual source Jacobi polynomial inside the angle interval.
Use: every zero comparison for the Liouville equation concerns the original finite Jacobi zeros.
Article: jacobi, Proposition B.1.
Proof: its actual real-power weight is strictly positive on the whole interior interval. -/
theorem liouville_zero_iff (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    liouville a b n t=0 ↔ realNormalized a b n (cos t)=0 := by
  rw [liouville,mul_eq_zero,or_iff_right (liouvilleWeight_pos a b ht).ne',angular_eq_realNormalized]

end
end jacobi.Jacobi
