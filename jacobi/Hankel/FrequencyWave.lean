import jacobi.Hankel.BesselWave
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
Article: jacobi, Lemma E.1.
Use: frequencyWave has the actual original Bessel zeros on the right half-plane, and its real restriction is the already proved real-ray Liouville function.
-/
namespace jacobi.Hankel
noncomputable section
open Set jacobi.Bessel
set_option backward.isDefEq.respectTransparency false

/-- The genuine complex-frequency Liouville prefactor, using the principal logarithm.
Use: frequencyWave has the actual original Bessel zeros on the right half-plane, and its real restriction is the already proved real-ray Liouville function.
Article: jacobi, Lemma E.1.
-/
def frequencyFactor (a z : ℂ) : ℂ := Complex.exp ((a+1/2)*Complex.log z)

/-- The original normalized Bessel function in the actual complex-frequency Liouville coordinate.
Use: complex-strip propagation and the subsequent original zero disks concern this same entire Bessel factor, not an abstract ODE candidate.
Article: jacobi, Lemma E.1.
-/
def frequencyWave (a z : ℂ) : ℂ := frequencyFactor a z*normalized a (z^2)

/-- The genuine displayed first complex-frequency derivative of the original Bessel Liouville wave.
Use: frequencyWave_hasDerivAt and frequencySlope_hasDerivAt provide the actual state propagated along complex frequency segments.
Article: jacobi, Lemma E.1.
-/
def frequencySlope (a z : ℂ) : ℂ := frequencyFactor a z*
  ((a+1/2)/z*normalized a (z^2)+2*z*deriv (normalized a) (z^2))

/-- The genuine displayed second complex-frequency derivative of the original Bessel Liouville wave.
Use: frequencyWave_equation proves the actual original complex-frequency inverse-square ODE.
Article: jacobi, Lemma E.1.
-/
def frequencyCurvature (a z : ℂ) : ℂ := frequencyFactor a z*
  ((a+1/2)*(a-1/2)/z^2*normalized a (z^2)+4*(a+1)*deriv (normalized a) (z^2)+
    4*z^2*deriv (deriv (normalized a)) (z^2))

/-- The true complex Liouville prefactor has its genuine logarithmic derivative away from the principal branch cut.
Use: frequencyWave_hasDerivAt computes the actual original Bessel wave derivative on every right-half-plane frequency segment.
Article: jacobi, Lemma E.1.
Proof: differentiate the genuine principal complex logarithm and exponential on the slit plane. -/
theorem frequencyFactor_hasDerivAt (a : ℂ) {z : ℂ} (hz : z∈Complex.slitPlane) :
    HasDerivAt (frequencyFactor a) (frequencyFactor a z*((a+1/2)/z)) z := by
  convert! ((Complex.hasDerivAt_log hz).const_mul (a+1/2)).cexp using 1

/-- The original complex-frequency Liouville Bessel wave has its actual displayed first derivative.
Use: the true complex Bessel state is propagated from the established real-ray asymptotic to the original zero disks.
Article: jacobi, Lemma E.1.
Proof: combine the genuine logarithmic prefactor derivative with the actual entire Bessel derivative composed with the complex square. -/
theorem frequencyWave_hasDerivAt (a : ℂ) {z : ℂ} (hz : z∈Complex.slitPlane) :
    HasDerivAt (frequencyWave a) (frequencySlope a z) z := by
  have hF := (normalized_analytic a (z^2)).differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).pow 2)
  convert! (frequencyFactor_hasDerivAt a hz).mul hF using 1
  simp only [frequencySlope,Function.comp_def,Pi.pow_apply,id_eq,Nat.reduceSub,pow_one,mul_one,Nat.cast_ofNat]
  ring

/-- The actual complex-frequency Bessel slope has its genuine displayed derivative on the principal slit plane.
Use: frequencyWave_equation gives the actual second-order complex ODE, including every frequency on the bounded vertical propagation segments.
Article: jacobi, Lemma E.1.
Proof: apply the ordinary complex quotient, product and chain rules to the actual slope; the original slit-plane frequency is nonzero. -/
theorem frequencySlope_hasDerivAt (a : ℂ) {z : ℂ} (hz : z∈Complex.slitPlane) :
    HasDerivAt (frequencySlope a) (frequencyCurvature a z) z := by
  -- Both spectral derivatives remain derivatives of the original normalized entire Bessel function.
  have hn : z≠0 := Complex.slitPlane_ne_zero hz
  have hF := (normalized_analytic a (z^2)).differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).pow 2)
  have hG := (normalized_analytic a (z^2)).deriv.differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).pow 2)
  have hp := ((hasDerivAt_const z (a+1/2)).div (hasDerivAt_id z) hn).mul hF
  have hq := ((hasDerivAt_id z).const_mul 2).mul hG
  convert! (frequencyFactor_hasDerivAt a hz).mul (hp.add hq) using 1
  simp only [frequencyCurvature,Function.comp_def,Pi.pow_apply,Pi.add_apply,Pi.mul_apply,
    Pi.div_apply,id_eq,Nat.reduceSub,pow_one,mul_one,Nat.cast_ofNat,zero_mul,zero_sub]
  field_simp
  ring

/-- The genuine original Bessel function satisfies its actual complex-frequency inverse-square Liouville equation.
Use: the normalized true Hankel error has a proved forced ODE on the right half-plane and may be propagated into the original complex zero disks.
Article: jacobi, Lemma E.1.
Proof: substitute the proved original complex derivatives and use the independently verified entire normalized Bessel equation; only its genuine nonzero frequency denominator is cleared. -/
theorem frequencyWave_equation {a z : ℂ} (ha : -1<a.re) (hz : z≠0) :
    frequencyCurvature a z+(1+(1/4-a^2)/z^2)*frequencyWave a z=0 := by
  have he := normalized_equation ha (z^2)
  unfold frequencyCurvature frequencyWave
  field_simp
  linear_combination 16*frequencyFactor a z*z^2*he

/-- The actual complex-frequency Bessel value and slope restrict to exactly the already proved original real-ray value and slope.
Use: complex propagation starts with the original established uniform real-ray error, so no replacement initial data are introduced.
Article: jacobi, Lemma E.1.
Proof: on a positive real coordinate the principal complex logarithm is the real logarithm included in the complex field; all original Bessel and rational factors are identical. -/
theorem frequencyWave_ofReal (a : ℂ) {x : ℝ} (hx : 0<x) :
    frequencyWave a (x:ℂ)=complexBesselWave a x ∧ frequencySlope a (x:ℂ)=complexBesselWaveSlope a x := by
  simp only [frequencyWave,frequencySlope,frequencyFactor,complexBesselWave,complexBesselWaveSlope,
    complexWaveFactor,← Complex.ofReal_log hx.le,and_self]

end
end jacobi.Hankel
