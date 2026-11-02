import jacobi.Jacobi.AngularEquation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Proposition B.1.
The source's singular sine/cosine weight is strictly positive inside
(0,pi). Its true derivative and the derivative of its logarithmic slope
are established throughout that interval for arbitrary real parameters.
Use: multiplication by this weight preserves exactly all actual angular zeros.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The literal positive interior weight in the Jacobi Liouville transformation.
Use: multiplication by this weight preserves exactly all actual angular zeros.
Article: jacobi, Proposition B.1.
-/
def liouvilleWeight (a b t : ℝ) : ℝ := sin (t/2)^(a+1/2)*cos (t/2)^(b+1/2)

/-- The exact logarithmic derivative of the singular Jacobi Liouville weight.
Use: cancels the actual angular first-derivative coefficient in the transformed equation.
Article: jacobi, Proposition B.1.
-/
def liouvilleLogSlope (a b t : ℝ) : ℝ :=
  (a+1/2)/2*(cos (t/2)/sin (t/2))-(b+1/2)/2*(sin (t/2)/cos (t/2))

/-- The explicit actual derivative of the Liouville logarithmic slope.
Use: evaluates the inverse-square singular potential after cancelling the first derivative.
Article: jacobi, Proposition B.1.
-/
def liouvilleLogAcceleration (a b t : ℝ) : ℝ :=
  -(a+1/2)/(4*sin (t/2)^2)-(b+1/2)/(4*cos (t/2)^2)

/-- Both half-angle bases are strictly positive throughout the actual angular interval.
Use: permits arbitrary real powers and every logarithmic-weight cancellation in the Liouville proof.
Article: jacobi, Proposition B.1.
Proof: the half-angle is between zero and pi/2, where sine and cosine are positive. -/
theorem half_angle_positive {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    0<sin (t/2) ∧ 0<cos (t/2) := by
  exact ⟨sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2,Real.pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2]⟩⟩

/-- The source's actual Liouville weight is strictly positive throughout the entire open angle interval.
Use: the transformed wave has exactly the same finite zeros as the original source polynomial.
Article: jacobi, Proposition B.1.
Proof: each base is strictly positive and every real power of a positive real number is positive. -/
theorem liouvilleWeight_pos (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    0<liouvilleWeight a b t :=
  mul_pos (rpow_pos_of_pos (half_angle_positive ht).1 _) (rpow_pos_of_pos (half_angle_positive ht).2 _)

/-- The logarithmic slope gives the actual ordinary derivative of the full singular Liouville weight.
Use: differentiates the actual transformed Jacobi wave in the complete endpoint-exponent range.
Article: jacobi, Proposition B.1.
Proof: differentiate the two positive half-angle real powers using the
community chain and product rules. Their positive bases justify the exact
real-power shifts that factor out the original weight. -/
theorem liouvilleWeight_hasDerivAt (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    HasDerivAt (liouvilleWeight a b) (liouvilleLogSlope a b t*liouvilleWeight a b t) t := by
  -- This proof uses real powers on their actual positive branches, including negative exponents.
  obtain ⟨hs,hc⟩ := half_angle_positive ht
  have hi := (hasDerivAt_id t).div_const 2
  have hS := (Real.hasDerivAt_sin (t/2)).comp t hi
  have hC := (Real.hasDerivAt_cos (t/2)).comp t hi
  have h1 := (Real.hasDerivAt_rpow_const (p := a+1/2) (Or.inl hs.ne')).comp t hS
  have h2 := (Real.hasDerivAt_rpow_const (p := b+1/2) (Or.inl hc.ne')).comp t hC
  convert h1.mul h2 using 1
  · rfl
  · dsimp only [liouvilleLogSlope,liouvilleWeight,Function.comp_apply,id_eq]
    rw [rpow_sub_one hs.ne',rpow_sub_one hc.ne']
    field_simp [hs.ne',hc.ne']
    ring

/-- The explicit logarithmic acceleration is the true derivative of the actual Liouville logarithmic slope.
Use: derives the inverse-square potential from genuine differentiation rather than an assumed transformed ODE.
Article: jacobi, Proposition B.1.
Proof: differentiate the two actual half-angle quotients. The identity
sin^2+cos^2=1 reduces each quotient derivative to its inverse-square form. -/
theorem liouvilleLogSlope_hasDerivAt (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    HasDerivAt (liouvilleLogSlope a b) (liouvilleLogAcceleration a b t) t := by
  -- Nonzero denominators follow from the previously established actual half-angle positivity.
  obtain ⟨hs,hc⟩ := half_angle_positive ht
  have hi := (hasDerivAt_id t).div_const 2
  have hS := (Real.hasDerivAt_sin (t/2)).comp t hi
  have hC := (Real.hasDerivAt_cos (t/2)).comp t hi
  have h1 := (hC.div hS hs.ne').const_mul ((a+1/2)/2)
  have h2 := (hS.div hC hc.ne').const_mul ((b+1/2)/2)
  convert h1.sub h2 using 1
  · rfl
  · dsimp only [liouvilleLogAcceleration,Function.comp_apply,id_eq]
    have he1 : ((-sin (t/2))*(1/2)*sin (t/2)-cos (t/2)*(cos (t/2)*(1/2)))/sin (t/2)^2=
        -1/(2*sin (t/2)^2) := by
      apply (div_eq_iff (pow_ne_zero 2 hs.ne')).mpr
      field_simp [hs.ne']
      nlinarith [sin_sq_add_cos_sq (t/2)]
    have he2 : ((cos (t/2))*(1/2)*cos (t/2)-sin (t/2)*((-sin (t/2))*(1/2)))/cos (t/2)^2=
        1/(2*cos (t/2)^2) := by
      apply (div_eq_iff (pow_ne_zero 2 hc.ne')).mpr
      field_simp [hc.ne']
      nlinarith [sin_sq_add_cos_sq (t/2)]
    rw [he1,he2]
    ring

end
end jacobi.Jacobi
