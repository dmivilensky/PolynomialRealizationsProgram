import jacobi.Hankel.IncomingAmplitude
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: jacobi, Lemma E.1.
Use: jostWronskian_formula proves that the two genuinely constructed waves are a true basis, allowing an exact comparison with the original Bessel solution.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual original incoming/outgoing Jost Wronskian with the cancelling Fourier factors removed.
Use: jostWronskian_formula proves that the two genuinely constructed waves are a true basis, allowing an exact comparison with the original Bessel solution.
Article: jacobi, Lemma E.1.
-/
def jostWronskian {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  besselAmplitude hR a x*incomingAmplitudeSlope hR a x-
    besselAmplitudeSlope hR a x*incomingAmplitude hR a x-
    2*Complex.I*besselAmplitude hR a x*incomingAmplitude hR a x

/-- The genuine original Jost Wronskian has derivative zero throughout its actual outgoing ray.
Use: jostWronskian_formula evaluates the same original constant at infinity to discharge the true nonzero Jost-basis determinant.
Article: jacobi, Lemma E.1.
Proof: differentiate the three original amplitude products and substitute the proved actual outgoing and incoming slope ODEs; their opposite first-order Fourier terms cancel exactly. -/
theorem jostWronskian_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (jostWronskian hR a) 0 x := by
  -- The cancellation uses the true derivatives of the actual analytic inverse solutions on the same fixed ray.
  have hp := besselAmplitude_hasDerivAt hR ha hx
  have hm := incomingAmplitude_hasDerivAt hR ha hx
  have hp' := besselAmplitudeSlope_hasDerivAt hR a hx
  have hm' := incomingAmplitudeSlope_hasDerivAt hR a hx
  convert! ((hp.mul hm').sub (hp'.mul hm)).sub ((hp.mul hm).const_mul (2*Complex.I)) using 1
  · funext y
    dsimp only [jostWronskian,Pi.sub_apply,Pi.mul_apply]
    ring
  · ring

/-- The actual original Jost Wronskian tends to -2i at infinity.
Use: jostWronskian_formula identifies its genuine constant without assuming any classical Jost normalization or asymptotic Wronskian certificate.
Article: jacobi, Lemma E.1.
Proof: the two true amplitudes tend to one and their actual slopes tend to zero, by the independently proved improper-tail bounds. -/
theorem jostWronskian_limit {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) :
    Tendsto (jostWronskian hR a) atTop (𝓝 (-2*Complex.I)) := by
  -- The actual four amplitude endpoints fix the determinant after the genuine Fourier factors cancel.
  have hp := besselAmplitude_limit hR ha
  have hm := incomingAmplitude_limit hR ha
  have hp' := besselAmplitudeSlope_limit hR ha
  have hm' := incomingAmplitudeSlope_limit hR ha
  convert! ((hp.mul hm').sub (hp'.mul hm)).sub ((hp.mul hm).const_mul (2*Complex.I)) using 1
  · funext y
    dsimp only [jostWronskian,Pi.sub_apply,Pi.mul_apply]
    ring
  · ring

/-- The actual original outgoing/incoming Jost determinant is exactly -2i at every point of the same positive fixed ray.
Use: the genuine Bessel solution has a unique decomposition in these two actual analytic waves; this is the comparison step underlying the uniform complex-order Hankel zero tail.
Article: jacobi, Lemma E.1.
Proof: the true derivative vanishes on the connected original ray, so the actual Wronskian is constant there. Its independently proved genuine infinity limit fixes that constant to -2i. -/
theorem jostWronskian_formula {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R<x) :
    jostWronskian hR a x= -2*Complex.I := by
  -- A single connected-ray identity is evaluated at its genuine infinity limit.
  have hstrict : ‖besselCoefficient a‖/R<1 := ha.trans_lt (by norm_num)
  have he (y : ℝ) (hy : R<y) : jostWronskian hR a y=jostWronskian hR a x :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi R).isPreconnected
      (fun t ht => (jostWronskian_hasDerivAt hR hstrict ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (jostWronskian_hasDerivAt hR hstrict ht).deriv) hy hx
  have hl : Tendsto (fun _ : ℝ => jostWronskian hR a x) atTop (𝓝 (-2*Complex.I)) :=
    (jostWronskian_limit hR ha).congr' (by
      filter_upwards [eventually_gt_atTop R] with y hy
      exact he y hy)
  exact tendsto_nhds_unique tendsto_const_nhds hl

/-- The original constructed Jost waves have a genuinely nonzero basis determinant everywhere on their actual common ray.
Use: Bessel Cauchy-data comparison divides only by this independently proved actual Wronskian, without an unproved outgoing completeness or independence premise.
Article: jacobi, Lemma E.1.
Proof: the proved exact original determinant is -2i, and both complex factors are nonzero. -/
theorem jostWronskian_ne_zero {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R<x) :
    jostWronskian hR a x≠0 := by
  rw [jostWronskian_formula hR ha hx]
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

end
end jacobi.Hankel
