import jacobi.Reference.Eigenfunctions

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The original sine-power prefactor has two genuine ordinary derivatives
on (0,1). Its logarithmic derivatives retain the selected branch for
all gamma>1/4, including the singular endpoint regime gamma<1/2.
Use: computes the actual reference eigenfunction derivatives and removes the Jacobi first-derivative term.
-/
namespace jacobi.Reference
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The exact logarithmic slope of the source reference prefactor.
Use: computes the actual reference eigenfunction derivatives and removes the Jacobi first-derivative term.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def weightLogSlope (a t : ℝ) : ℝ := gamma a*Real.pi*cos (Real.pi*t)/sin (Real.pi*t)

/-- The exact logarithmic acceleration of the actual reference prefactor.
Use: identifies the original Poeschl--Teller singular potential in the true second derivative.
Article: jacobi, Lemma C.1.
-/
def weightLogAcceleration (a t : ℝ) : ℝ := -gamma a*Real.pi^2/sin (Real.pi*t)^2

/-- Every actual physical reference angle has positive sine.
Use: justifies all real-power and quotient derivative formulas on the full interior.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: multiply the original interval inequalities by positive pi. -/
theorem sine_pos {t : ℝ} (ht : t∈Ioo 0 1) : 0<sin (Real.pi*t) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1) (by nlinarith [Real.pi_pos,ht.2])

/-- The explicit logarithmic slope gives the actual first derivative of the source reference prefactor.
Use: the reference polynomial eigenfunctions obey a genuine classical equation, rather than a formal transformed equation.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: differentiate the positive sine-over-pi base and its actual real power; the real-power shift factors out the original prefactor. -/
theorem weight_hasDerivAt (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (weight a) (weightLogSlope a t*weight a t) t := by
  -- Only positive interior bases are used; no endpoint differentiability of the singular power is assumed.
  have hs := sine_pos ht
  have hb : 0<sin (Real.pi*t)/Real.pi := div_pos hs Real.pi_pos
  have hi := (hasDerivAt_id t).const_mul Real.pi
  have hsin := ((Real.hasDerivAt_sin (Real.pi*t)).comp t hi).div_const Real.pi
  convert ((Real.hasDerivAt_rpow_const (p := gamma a) (Or.inl hb.ne')).comp t hsin) using 1
  · rfl
  · dsimp [weightLogSlope,weight]
    rw [Real.rpow_sub_one hb.ne']
    field_simp [hs.ne',Real.pi_ne_zero]

/-- The actual logarithmic slope has precisely the printed inverse-sine-square derivative.
Use: completes the true second derivative of the actual reference prefactor.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the quotient rule and sin^2+cos^2=1 simplify the genuine derivative. -/
theorem weightLogSlope_hasDerivAt (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (weightLogSlope a) (weightLogAcceleration a t) t := by
  -- The denominator nonvanishing follows from the original physical interval, not from a separate admissibility hypothesis.
  have hs := sine_pos ht
  have hi := (hasDerivAt_id t).const_mul Real.pi
  have hc := (Real.hasDerivAt_cos (Real.pi*t)).comp t hi
  have hsin := (Real.hasDerivAt_sin (Real.pi*t)).comp t hi
  convert ((hc.const_mul (gamma a*Real.pi)).div hsin hs.ne') using 1
  · rfl
  · dsimp [weightLogAcceleration]
    field_simp [hs.ne']
    nlinarith [congrArg (fun x : ℝ => gamma a*x) (Real.sin_sq_add_cos_sq (Real.pi*t))]

/-- The actual reference prefactor is real analytic at every physical interior point.
Use: supplies continuity of all original reference derivatives and the selected classical solution regularity.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the analytic sine-over-pi base is positive; reuse the proved analytic positive-power composition lemma. -/
theorem weight_analytic (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) : AnalyticAt ℝ (weight a) t := by
  apply jacobi.Jacobi.analytic_positive_rpow
    ((Real.analyticAt_sin.comp (f := fun s : ℝ => Real.pi*s) (analyticAt_const.mul analyticAt_id)).div_const)
  exact div_pos (sine_pos ht) Real.pi_pos

end
end jacobi.Reference
