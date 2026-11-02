import jacobi.Hankel.JostLimits
import jacobi.Hankel.CubicRemainder
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.ContinuousMap.Bounded.Star

/-!
Article: jacobi, Lemma E.1.
Its holomorphic order dependence, true Liouville derivatives and
normalizations at infinity are proved for this actual solution.
Together with the outgoing wave it gives a genuine common-order
Jost basis for comparison with the original entire Bessel function.
Use: incomingAmplitude is a genuine solution at the same original order as outgoingAmplitude, rather than at its conjugate order.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The true original complex Bessel coefficient respects order conjugation.
Use: incomingAmplitude is a genuine solution at the same original order as outgoingAmplitude, rather than at its conjugate order.
Article: jacobi, Lemma E.1.
Proof: conjugation preserves the original real coefficients and integer square. -/
theorem besselCoefficient_star (a : ℂ) : besselCoefficient (star a)=star (besselCoefficient a) := by
  simp [besselCoefficient]

/-- The original incoming normalized Bessel amplitude on the same fixed real ray.
Use: its actual spatial derivatives and infinity limits construct the genuine incoming Jost solution in the original complex-order Bessel comparison.
Article: jacobi, Lemma E.1.
-/
def incomingAmplitude {R : ℝ} (hR : 0<R) (a : ℂ) : OutgoingSpace :=
  star (besselAmplitude hR (star a))

/-- The actual spatial slope of the original incoming normalized Bessel amplitude.
Use: incomingAmplitudeSlope_hasDerivAt supplies the original incoming amplitude ODE and the true Jost Wronskian.
Article: jacobi, Lemma E.1.
-/
def incomingAmplitudeSlope {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  star (besselAmplitudeSlope hR (star a) x)

/-- The genuine incoming amplitude is holomorphic in the original complex order on the same actual contraction domain as the outgoing amplitude.
Use: the two original Jost waves provide an actual holomorphic basis for the Bessel coefficients and the common high-index zero continuation.
Article: jacobi, Lemma E.1.
Proof: conjugating both the true analytic outgoing function and its complex argument preserves complex differentiability. The actual contraction domain is open and invariant under conjugation, so the community complex differentiability theorem gives Banach-valued analyticity there. -/
theorem incomingAmplitude_analytic {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) : AnalyticAt ℂ (incomingAmplitude hR) a := by
  -- Both conjugations are essential: one conjugation alone would not preserve complex analyticity.
  have hU : IsOpen {b : ℂ | ‖besselCoefficient b‖/R<1} :=
    isOpen_lt (by unfold besselCoefficient; fun_prop) continuous_const
  apply DifferentiableOn.analyticAt (s := {b : ℂ | ‖besselCoefficient b‖/R<1}) ?_ (hU.mem_nhds ha)
  intro b hb
  change ‖besselCoefficient b‖/R<1 at hb
  have hbc : ‖besselCoefficient (star b)‖/R<1 := by
    simpa only [besselCoefficient_star,norm_star] using hb
  have hd := (besselAmplitude_analytic hR hbc).differentiableAt.star_conj
  have he : DifferentiableAt ℂ (incomingAmplitude hR) b := by
    simp only [Function.comp_def,← Complex.star_def,star_star] at hd
    convert! hd using 1
  exact he.differentiableWithinAt

/-- The original incoming normalized Bessel amplitude has its stated genuine spatial derivative on the same positive fixed ray.
Use: the actual incoming wave has the genuine Cauchy data required for the true Bessel Jost decomposition.
Article: jacobi, Lemma E.1.
Proof: apply real-parameter conjugation to the actual outgoing derivative at conjugate order; the genuine Bessel contraction condition is invariant under order conjugation. -/
theorem incomingAmplitude_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (fun y : ℝ => incomingAmplitude hR a y) (incomingAmplitudeSlope hR a x) x := by
  have hbc : ‖besselCoefficient (star a)‖/R<1 := by
    simpa only [besselCoefficient_star,norm_star] using ha
  exact (besselAmplitude_hasDerivAt hR hbc hx).star

/-- The actual incoming Bessel amplitude slope has its true original inverse-square differential equation.
Use: the incoming and outgoing waves solve the same genuine second-order Liouville equation, permitting an actual constant-Wronskian comparison with the original Bessel solution.
Article: jacobi, Lemma E.1.
Proof: conjugate the already proved genuine outgoing slope equation at conjugate order, cancel the two coefficient conjugations and use the real spatial coordinate. -/
theorem incomingAmplitudeSlope_hasDerivAt {R : ℝ} (hR : 0<R) (a : ℂ)
    {x : ℝ} (hx : R<x) :
    HasDerivAt (incomingAmplitudeSlope hR a)
      (2*Complex.I*incomingAmplitudeSlope hR a x-
        besselCoefficient a/(x:ℂ)^2*incomingAmplitude hR a x) x := by
  convert! (besselAmplitudeSlope_hasDerivAt hR (star a) hx).star using 1
  simp [incomingAmplitudeSlope,incomingAmplitude,besselCoefficient]

/-- The actual original incoming Bessel amplitude tends to its genuine normalization one at infinity.
Use: fixes the true outgoing/incoming Wronskian and the original Bessel phase without assuming either infinity endpoint.
Article: jacobi, Lemma E.1.
Proof: conjugate the actual outgoing limit at conjugate order, whose true half-contraction bound is the same original coefficient bound. -/
theorem incomingAmplitude_limit {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) :
    Tendsto (fun x : ℝ => incomingAmplitude hR a x) atTop (𝓝 1) := by
  have hbc : ‖besselCoefficient (star a)‖/R≤1/2 := by
    simpa only [besselCoefficient_star,norm_star] using ha
  convert! (besselAmplitude_limit hR hbc).star using 1
  simp only [star_one]

/-- The true spatial slope of the original incoming Bessel amplitude tends to zero at infinity.
Use: the actual incoming/outgoing Wronskian is evaluated by its genuine infinity limits in the uniform complex-order Bessel comparison.
Article: jacobi, Lemma E.1.
Proof: conjugate the proved true outgoing slope limit at conjugate order and use the actual coefficient norm invariance. -/
theorem incomingAmplitudeSlope_limit {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) :
    Tendsto (incomingAmplitudeSlope hR a) atTop (𝓝 0) := by
  have hbc : ‖besselCoefficient (star a)‖/R≤1/2 := by
    simpa only [besselCoefficient_star,norm_star] using ha
  convert! (besselAmplitudeSlope_limit hR hbc).star using 1
  simp only [star_zero]

end
end jacobi.Hankel
