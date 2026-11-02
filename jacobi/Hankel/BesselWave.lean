import jacobi.Bessel.Differential
import jacobi.Bessel.OrderShift
import jacobi.Analytic.BesselOrder
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: jacobi, Lemma E.1.
Use: complexBesselWave is exactly the original normalized Bessel series multiplied by x^(alpha+1/2), with its real-positive logarithm fixing the branch.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original complex-order Liouville prefactor on the positive real spatial ray.
Use: complexBesselWave is exactly the original normalized Bessel series multiplied by x^(alpha+1/2), with its real-positive logarithm fixing the branch.
Article: jacobi, Lemma E.1.
-/
def complexWaveFactor (a : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((a+1/2)*(Real.log x:ℂ))

/-- The actual original complex-order normalized Bessel function in Liouville form.
Use: complexBesselWave_equation identifies the genuine Bessel solution of the same outgoing inverse-square equation used by the uniform complex-order Jost construction.
Article: jacobi, Lemma E.1.
-/
def complexBesselWave (a : ℂ) (x : ℝ) : ℂ :=
  complexWaveFactor a x*normalized a ((x:ℂ)^2)

/-- The actual explicit spatial slope of the original complex-order Liouville Bessel wave.
Use: its true derivative and order analyticity determine the original Bessel coefficients in the outgoing/incoming basis.
Article: jacobi, Lemma E.1.
-/
def complexBesselWaveSlope (a : ℂ) (x : ℝ) : ℂ :=
  complexWaveFactor a x*((a+1/2)/(x:ℂ)*normalized a ((x:ℂ)^2)+
    2*(x:ℂ)*deriv (normalized a) ((x:ℂ)^2))

/-- The actual explicit spatial curvature of the original complex-order Liouville Bessel wave.
Use: complexBesselWave_equation cancels its actual normalized Bessel spectral derivatives using the proved entire differential equation.
Article: jacobi, Lemma E.1.
-/
def complexBesselWaveCurvature (a : ℂ) (x : ℝ) : ℂ :=
  complexWaveFactor a x*((a+1/2)*(a-1/2)/(x:ℂ)^2*normalized a ((x:ℂ)^2)+
    4*(a+1)*deriv (normalized a) ((x:ℂ)^2)+
    4*(x:ℂ)^2*deriv (deriv (normalized a)) ((x:ℂ)^2))

/-- The original complex-order positive-ray Liouville prefactor has its actual logarithmic spatial derivative.
Use: both derivatives of the genuine Bessel wave are calculated without a branch-dependent power differentiation premise.
Article: jacobi, Lemma E.1.
Proof: differentiate the true positive-axis real logarithm, include its derivative in the complex plane, and apply the actual complex exponential chain rule. -/
theorem complexWaveFactor_hasDerivAt (a : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (complexWaveFactor a) (complexWaveFactor a x*((a+1/2)/(x:ℂ))) x := by
  -- The original spatial logarithm is differentiated at its genuine positive, nonzero point.
  have hl := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (Real.hasDerivAt_log hx.ne')
  convert! (hl.const_mul (a+1/2)).cexp using 1
  simp only [complexWaveFactor,Function.comp_def,Complex.ofRealCLM_apply,
    Complex.ofReal_inv,div_eq_mul_inv]

/-- The original complex-order Liouville Bessel wave has its stated genuine spatial derivative.
Use: its actual Cauchy data are compared with the true outgoing/incoming waves in the uniform complex-order Hankel argument.
Article: jacobi, Lemma E.1.
Proof: apply the actual product rule to its true logarithmic prefactor and the complex Bessel derivative composed with the squared real inclusion. -/
theorem complexBesselWave_hasDerivAt (a : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (complexBesselWave a) (complexBesselWaveSlope a x) x := by
  have hd : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  have hF := (normalized_analytic a ((x:ℂ)^2)).differentiableAt.hasDerivAt.comp x (hd.pow 2)
  convert! (complexWaveFactor_hasDerivAt a hx).mul hF using 1
  simp only [complexBesselWaveSlope,Function.comp_def,Pi.pow_apply,Nat.reduceSub,pow_one,mul_one,Nat.cast_ofNat]
  ring

/-- The original explicit complex-order Bessel slope has the stated genuine second spatial derivative.
Use: complexBesselWave_equation concerns a true second-order solution, allowing actual Wronskian and ODE uniqueness arguments with the constructed Jost waves.
Article: jacobi, Lemma E.1.
Proof: differentiate the original two slope factors, use both true complex spectral derivatives of the original entire Bessel function, and collect the actual nonzero spatial denominator. -/
theorem complexBesselWaveSlope_hasDerivAt (a : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (complexBesselWaveSlope a) (complexBesselWaveCurvature a x) x := by
  -- Every spectral derivative belongs to the same original normalized entire Bessel function.
  have hz : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hd : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  have hF := (normalized_analytic a ((x:ℂ)^2)).differentiableAt.hasDerivAt.comp x (hd.pow 2)
  have hG := (normalized_analytic a ((x:ℂ)^2)).deriv.differentiableAt.hasDerivAt.comp x (hd.pow 2)
  have hP := ((hasDerivAt_const x (a+1/2)).div hd hz).mul hF
  have hQ := (hd.const_mul 2).mul hG
  convert! (complexWaveFactor_hasDerivAt a hx).mul (hP.add hQ) using 1
  simp only [complexBesselWaveCurvature,Function.comp_def,Pi.pow_apply,Pi.add_apply,
    Pi.mul_apply,Pi.div_apply,Nat.reduceSub,pow_one,mul_one,Nat.cast_ofNat,zero_mul,zero_sub]
  field_simp
  ring

/-- The actual original complex-order Bessel wave satisfies the same genuine inverse-square Liouville equation as the constructed Jost waves.
Use: their actual Wronskians and Cauchy data identify the Bessel solution and its common complex-order Hankel expansion, required for the uniform continuation of the numbered zero tail.
Article: jacobi, Lemma E.1.
Proof: the original entire normalized Bessel differential equation cancels its genuine spectral derivatives; the remaining prefactor coefficient is exactly alpha^2-1/4. -/
theorem complexBesselWave_equation {a : ℂ} (ha : -1<a.re) {x : ℝ} (hx : 0<x) :
    complexBesselWaveCurvature a x+(1+(1/4-a^2)/(x:ℂ)^2)*complexBesselWave a x=0 := by
  have hz : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he := normalized_equation ha ((x:ℂ)^2)
  unfold complexBesselWaveCurvature complexBesselWave
  field_simp
  linear_combination 16*complexWaveFactor a x*(x:ℂ)^2*he

end
end jacobi.Hankel
