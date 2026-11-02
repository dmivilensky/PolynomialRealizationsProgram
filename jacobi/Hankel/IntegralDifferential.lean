import jacobi.Hankel.FourierTail

/-!
Article: jacobi, Lemma E.1.
Use: outgoingIntegral_hasDerivAt and outgoingSlope_hasDerivAt give the actual second-order amplitude equation.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The explicit genuine first spatial derivative of the original outgoing integral.
Use: outgoingIntegral_hasDerivAt and outgoingSlope_hasDerivAt give the actual second-order amplitude equation.
Article: jacobi, Lemma E.1.
-/
def outgoingSlope (m : ℝ → ℝ) (f : OutgoingSpace) (x : ℝ) : ℂ :=
  -Complex.exp (-2*(x:ℂ)*Complex.I)*
    tailPrimitive (fun y : ℝ => Complex.exp (2*(y:ℂ)*Complex.I)*((m y:ℂ)*f y)) x

/-- The two original opposite Fourier factors multiply exactly to one.
Use: the genuine Fourier-tail derivatives cancel their moving-endpoint source terms in outgoingIntegral_hasDerivAt.
Article: jacobi, Lemma E.1.
Proof: combine the original two complex exponentials and cancel their opposite exponents. -/
theorem outgoingFourier_cancel (x : ℝ) :
    Complex.exp (-2*(x:ℂ)*Complex.I)*Complex.exp (2*(x:ℂ)*Complex.I)=1 := by
  rw [← Complex.exp_add]
  ring_nf
  exact Complex.exp_zero

/-- The actual outgoing integral has the stated genuine spatial derivative at every original continuity point of the measurable potential.
Use: Jost differentiation refers to the very same bounded-continuous integral operator whose true inverse is analytic in complex order.
Article: jacobi, Lemma E.1.
Proof: apply the proved improper FTC to the two actual integrable Fourier tails, differentiate their exact exponential factor, and cancel the genuine moving-endpoint terms. -/
theorem outgoingIntegral_hasDerivAt {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m)
    (f : OutgoingSpace) {x : ℝ} (hc : ContinuousAt m x) :
    HasDerivAt (outgoingIntegral m f) (outgoingSlope m f x) x := by
  -- All improper tails have already been proved absolutely integrable before the FTC is applied.
  have hsrc : StronglyMeasurable (fun y : ℝ => (m y:ℂ)*f y) :=
    (hmm.complex_ofReal.mul f.continuous.measurable).stronglyMeasurable
  have hcont : ContinuousAt (fun y : ℝ => (m y:ℂ)*f y) x := hc.ofReal.mul f.continuous.continuousAt
  have hfou : Continuous (fun y : ℝ => Complex.exp (2*(y:ℂ)*Complex.I)) := by fun_prop
  have hA := tailPrimitive_hasDerivAt (outgoingFourier_integrable (outgoingSource_integrable hm f))
    (hfou.stronglyMeasurable.mul hsrc) (hfou.continuousAt.mul hcont)
  have hB := tailPrimitive_hasDerivAt (outgoingSource_integrable hm f) hsrc hcont
  have hd : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  have hE := (((hd.const_mul (-2)).mul_const Complex.I).cexp)
  convert! ((hE.mul hA).sub hB).div_const (2*Complex.I) using 1
  · exact funext (outgoingIntegral_fourierTail hm f)
  · simp only [outgoingSlope]
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℂ)≠0) Complex.I_ne_zero)).mpr
    linear_combination ((m x:ℂ)*f x)*(outgoingFourier_cancel x)

/-- The genuine first outgoing derivative satisfies its actual second spatial equation at every original continuity point of the measurable potential.
Use: the constructed outgoing Jost amplitude satisfies v''+2iv'+c*m*v=0 as an actual differential equation.
Article: jacobi, Lemma E.1.
Proof: differentiate its actual oscillatory tail by the improper FTC and use the exact inverse Fourier factor identity. -/
theorem outgoingSlope_hasDerivAt {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m)
    (f : OutgoingSpace) {x : ℝ} (hc : ContinuousAt m x) :
    HasDerivAt (outgoingSlope m f) (-2*Complex.I*outgoingSlope m f x+(m x:ℂ)*f x) x := by
  -- The same actual tail occurs in the derivative and in the original integral, so the ODE is an identity for one concrete solution.
  have hsrc : StronglyMeasurable (fun y : ℝ => (m y:ℂ)*f y) :=
    (hmm.complex_ofReal.mul f.continuous.measurable).stronglyMeasurable
  have hcont : ContinuousAt (fun y : ℝ => (m y:ℂ)*f y) x := hc.ofReal.mul f.continuous.continuousAt
  have hfou : Continuous (fun y : ℝ => Complex.exp (2*(y:ℂ)*Complex.I)) := by fun_prop
  have hA := tailPrimitive_hasDerivAt (outgoingFourier_integrable (outgoingSource_integrable hm f))
    (hfou.stronglyMeasurable.mul hsrc) (hfou.continuousAt.mul hcont)
  have hd : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  convert! ((((hd.const_mul (-2)).mul_const Complex.I).cexp).neg).mul hA using 1
  simp only [outgoingSlope,Pi.neg_apply]
  linear_combination -((m x:ℂ)*f x)*(outgoingFourier_cancel x)

end
end jacobi.Hankel
