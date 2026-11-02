import jacobi.Hankel.BesselWave
import jacobi.Hankel.JostWronskian

/-!
Article: jacobi, Lemma E.1.
Use: outgoing and incoming Bessel connection coefficients retain their genuine spatial Fourier factors.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The original real-ray exponential phase with an arbitrary complex coefficient.
Use: outgoing and incoming Bessel connection coefficients retain their genuine spatial Fourier factors.
Article: jacobi, Lemma E.1.
-/
def realPhase (c : ℂ) (x : ℝ) : ℂ := Complex.exp (c*(x:ℂ))

/-- The genuine Fourier phase has its actual real spatial derivative.
Use: the true Bessel connection coefficients have derivative zero after their opposite original phase factor is included.
Article: jacobi, Lemma E.1.
Proof: include the actual real coordinate by its complex continuous linear map and apply the complex exponential chain rule. -/
theorem realPhase_hasDerivAt (c : ℂ) (x : ℝ) :
    HasDerivAt (realPhase c) (c*realPhase c x) x := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  convert! (hd.const_mul c).cexp using 1
  simp only [realPhase,Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one]
  ring

/-- The true outgoing Bessel connection numerator formed from the original Bessel Cauchy data and the actual incoming amplitude.
Use: its actual spatial derivative is i times itself, so outgoingConnection is constant on the original far ray.
Article: jacobi, Lemma E.1.
-/
def outgoingConnectionNumerator {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  complexBesselWave a x*incomingAmplitudeSlope hR a x-
    complexBesselWaveSlope a x*incomingAmplitude hR a x-
    Complex.I*complexBesselWave a x*incomingAmplitude hR a x

/-- The true incoming Bessel connection numerator formed from the original Bessel Cauchy data and the actual outgoing amplitude.
Use: its actual spatial derivative is minus i times itself, so incomingConnection is constant on the original far ray.
Article: jacobi, Lemma E.1.
-/
def incomingConnectionNumerator {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  complexBesselWaveSlope a x*besselAmplitude hR a x-
    complexBesselWave a x*besselAmplitudeSlope hR a x-
    Complex.I*complexBesselWave a x*besselAmplitude hR a x

/-- The genuine outgoing mixed Bessel-Jost numerator has its exact original first-order spatial equation.
Use: outgoingConnection_hasDerivAt proves the true Bessel outgoing coefficient constant, without assuming an outgoing Bessel expansion.
Article: jacobi, Lemma E.1.
Proof: differentiate the three actual products and substitute the independently proved incoming-amplitude and original Bessel Liouville equations. -/
theorem outgoingConnectionNumerator_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (outgoingConnectionNumerator hR a)
      (Complex.I*outgoingConnectionNumerator hR a x) x := by
  -- The original Bessel curvature and the actual incoming slope derivative solve the very same inverse-square equation.
  have hxp := hR.trans hx
  have hY := complexBesselWave_hasDerivAt a hxp
  have hY' := complexBesselWaveSlope_hasDerivAt a hxp
  have hm := incomingAmplitude_hasDerivAt hR hc hx
  have hm' := incomingAmplitudeSlope_hasDerivAt hR a hx
  have he := complexBesselWave_equation ha hxp
  convert! ((hY.mul hm').sub (hY'.mul hm)).sub ((hY.mul hm).const_mul Complex.I) using 1
  · funext y
    dsimp only [outgoingConnectionNumerator,Pi.sub_apply,Pi.mul_apply]
    ring
  · dsimp only [outgoingConnectionNumerator,besselCoefficient]
    linear_combination incomingAmplitude hR a x*he-
      (complexBesselWave a x*incomingAmplitude hR a x)*Complex.I_sq

/-- The genuine incoming mixed Bessel-Jost numerator has its exact original first-order spatial equation.
Use: incomingConnection_hasDerivAt proves the true incoming Bessel coefficient constant on the common original ray.
Article: jacobi, Lemma E.1.
Proof: apply the actual product rules to the original Bessel and outgoing-amplitude Cauchy data and substitute their proved genuine Liouville equations. -/
theorem incomingConnectionNumerator_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (incomingConnectionNumerator hR a)
      (-Complex.I*incomingConnectionNumerator hR a x) x := by
  -- The original outgoing and Bessel equations cancel the true potential terms in this mixed Wronskian.
  have hxp := hR.trans hx
  have hY := complexBesselWave_hasDerivAt a hxp
  have hY' := complexBesselWaveSlope_hasDerivAt a hxp
  have hp := besselAmplitude_hasDerivAt hR hc hx
  have hp' := besselAmplitudeSlope_hasDerivAt hR a hx
  have he := complexBesselWave_equation ha hxp
  convert! ((hY'.mul hp).sub (hY.mul hp')).sub ((hY.mul hp).const_mul Complex.I) using 1
  · funext y
    dsimp only [incomingConnectionNumerator,Pi.sub_apply,Pi.mul_apply]
    ring
  · dsimp only [incomingConnectionNumerator,besselCoefficient]
    linear_combination -(besselAmplitude hR a x)*he+
      (complexBesselWave a x*besselAmplitude hR a x)*Complex.I_sq

/-- The actual original outgoing Bessel connection coefficient evaluated by its genuine Cauchy data at the current spatial point.
Use: bessel_decomposition evaluates this same spatially constant coefficient at one fixed common point, giving the true original Bessel Jost expansion.
Article: jacobi, Lemma E.1.
-/
def outgoingConnection {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  realPhase (-Complex.I) x*outgoingConnectionNumerator hR a x/(-2*Complex.I)

/-- The actual original incoming Bessel connection coefficient evaluated by its genuine Cauchy data at the current spatial point.
Use: bessel_decomposition combines the two true constant coefficients with the actual outgoing and incoming waves.
Article: jacobi, Lemma E.1.
-/
def incomingConnection {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  realPhase Complex.I x*incomingConnectionNumerator hR a x/(-2*Complex.I)

/-- The actual outgoing Bessel connection coefficient has zero genuine spatial derivative throughout the common original ray.
Use: outgoingConnection_constant evaluates the same original coefficient at the fixed cutoff-plus-one point for every spectral index.
Article: jacobi, Lemma E.1.
Proof: differentiate its original opposite phase factor and use the proved i-times-numerator equation; the two actual terms cancel. -/
theorem outgoingConnection_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (outgoingConnection hR a) 0 x := by
  convert! ((realPhase_hasDerivAt (-Complex.I) x).mul
    (outgoingConnectionNumerator_hasDerivAt hR ha hc hx)).div_const (-2*Complex.I) using 1
  ring

/-- The actual incoming Bessel connection coefficient has zero genuine spatial derivative throughout the common original ray.
Use: incomingConnection_constant evaluates the genuine incoming coefficient at the same fixed point as its outgoing counterpart.
Article: jacobi, Lemma E.1.
Proof: the actual positive phase derivative cancels the true minus-i numerator derivative in the ordinary product rule. -/
theorem incomingConnection_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (incomingConnection hR a) 0 x := by
  convert! ((realPhase_hasDerivAt Complex.I x).mul
    (incomingConnectionNumerator_hasDerivAt hR ha hc hx)).div_const (-2*Complex.I) using 1
  ring

end
end jacobi.Hankel
