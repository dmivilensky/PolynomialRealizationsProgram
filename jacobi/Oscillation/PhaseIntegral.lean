import jacobi.Oscillation.NormalizedFrame
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Proposition B.1.
The phase is the literal integral of the actual normalized-state rotation
speed. Its derivative is proved by the fundamental theorem of calculus,
with genuine interval integrability and measurability. No phase function
or differentiability certificate is supplied as an extra premise.
Use: constructs one continuous ordinary Pruefer angle from actual state integrals, for both original Bessel and Jacobi functions.
-/
namespace jacobi.Oscillation.RestoringSolution
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {I : Set ℝ} (S : RestoringSolution I)

/-- The true phase increment of the original restoring solution from a specified base point.
Use: constructs one continuous ordinary Pruefer angle from actual state integrals, for both original Bessel and Jacobi functions.
Article: jacobi, Proposition B.1.
-/
def phase (base x : ℝ) : ℝ := ∫ t in base..x,S.phaseDensity t

/-- The actual phase speed is measurable on the real line.
Use: justifies the local measurable hypothesis of the genuine phase integral's fundamental theorem of calculus.
Article: jacobi, Proposition B.1.
Proof: the original state and potential are measurable, and square root, arithmetic and total division preserve measurability. -/
theorem phaseDensity_measurable : Measurable S.phaseDensity := by
  have hf := S.value_measurable
  have hg := S.slope_measurable
  have hq := S.potential_measurable
  unfold phaseDensity amplitude energy
  fun_prop

/-- The actual rotation speed is continuous at every physical domain point.
Use: the true phase increment is classically differentiable throughout the original comparison interval.
Article: jacobi, Proposition B.1.
Proof: the actual solution and slope are differentiable, the original
coefficient is continuous, and the true amplitude denominator is strictly positive. -/
theorem phaseDensity_continuousAt {x : ℝ} (hx : x∈I) : ContinuousAt S.phaseDensity x := by
  have hf := (S.first x hx).continuousAt
  have hg := (S.second x hx).continuousAt
  have hq := S.potential_continuous x hx
  have hr := (S.amplitude_hasDerivAt hx).continuousAt
  exact ((hg.pow 2).add (hq.mul (hf.pow 2))).div (hr.pow 2)
    (pow_ne_zero 2 (S.amplitude_pos hx).ne')

/-- The literal phase integral over any physical joining interval is genuinely convergent.
Use: every phase difference is an actual convergent integral, including in the later asymptotic integration by parts.
Article: jacobi, Proposition B.1.
Proof: convexity keeps the compact joining interval inside the actual
physical domain, where the genuine phase speed is continuous. -/
theorem phase_intervalIntegrable (hI : Convex ℝ I) {base x : ℝ} (hb : base∈I) (hx : x∈I) :
    IntervalIntegrable S.phaseDensity volume base x := by
  have hc : ContinuousOn S.phaseDensity (uIcc base x) := fun t ht =>
    (S.phaseDensity_continuousAt (hI.ordConnected.uIcc_subset hb hx ht)).continuousWithinAt
  exact hc.intervalIntegrable

/-- The actual ordinary derivative of the constructed phase is precisely the original normalized-state rotation speed.
Use: provides the true phase equation needed for McMahon's cubic remainder and the uniform Jacobi perturbation estimate.
Article: jacobi, Proposition B.1.
Proof: the literal phase integral is genuinely integrable on the joining
interval and its original measurable integrand is continuous at the target
point. Apply the community fundamental theorem of calculus with all these hypotheses discharged. -/
theorem phase_hasDerivAt (hI : Convex ℝ I) {base x : ℝ} (hb : base∈I) (hx : x∈I) :
    HasDerivAt (S.phase base) (S.phaseDensity x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (S.phase_intervalIntegrable hI hb hx)
    S.phaseDensity_measurable.stronglyMeasurable.stronglyMeasurableAtFilter
    (S.phaseDensity_continuousAt hx)

/-- The genuine phase increment is exactly zero at its actual base point.
Use: fixes the constructed continuous phase branch without a free additive phase constant.
Article: jacobi, Proposition B.1.
Proof: its literal integral has equal endpoints. -/
theorem phase_self (base : ℝ) : S.phase base base=0 := by
  simp only [phase,intervalIntegral.integral_same]

end
end jacobi.Oscillation.RestoringSolution
