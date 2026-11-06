import chebyshev1.Nonlinear.PrefixSecondOrderLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The limiting prefix profile increases strictly to π/2. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology Interval

theorem prefixSecondOrderIntegral_hasDerivAt {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun a : ℝ => a*prefixSecondOrderIntegral a)
      ((∫ x in (0:ℝ)..a, x/cosh x)/a^2) a := by
  let S := fun a : ℝ => ∫ x in (0:ℝ)..a, 1/cosh x
  let M := fun a : ℝ => ∫ x in (0:ℝ)..a, x/cosh x
  have hcS : Continuous (fun x : ℝ => 1/cosh x) :=
    continuous_const.div continuous_cosh (fun x => (cosh_pos x).ne')
  have hcM : Continuous (fun x : ℝ => x/cosh x) :=
    continuous_id.div continuous_cosh (fun x => (cosh_pos x).ne')
  have hS : HasDerivAt S (1/cosh a) a :=
    intervalIntegral.integral_hasDerivAt_right (hcS.intervalIntegrable 0 a)
      hcS.stronglyMeasurable.stronglyMeasurableAtFilter hcS.continuousAt
  have hM : HasDerivAt M (a/cosh a) a :=
    intervalIntegral.integral_hasDerivAt_right (hcM.intervalIntegrable 0 a)
      hcM.stronglyMeasurable.stronglyMeasurableAtFilter hcM.continuousAt
  have hh := hS.sub (hM.div (hasDerivAt_id a) ha)
  simp only [id_eq, mul_one] at hh
  have hcoeff : 1/cosh a - ((a/cosh a)*a-M a)/a^2 = M a/a^2 := by field_simp; ring
  rw [hcoeff] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ha] with b hb
  change b*prefixSecondOrderIntegral b = S b-M b/b
  rw [prefixSecondOrderIntegral_decompose hb]
  dsimp [S, M]
  ring

theorem prefixSecondOrderIntegral_strictMonoOn :
    StrictMonoOn (fun a : ℝ => a*prefixSecondOrderIntegral a) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0:ℝ))
  · intro a ha
    exact (prefixSecondOrderIntegral_hasDerivAt ha.ne').continuousAt.continuousWithinAt
  · intro a ha
    have ha' : 0 < a := by simpa using ha
    rw [(prefixSecondOrderIntegral_hasDerivAt ha'.ne').deriv]
    apply div_pos _ (sq_pos_of_ne_zero ha'.ne')
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_id.div continuous_cosh (fun x => (cosh_pos x).ne')).intervalIntegrable 0 a)
      (fun x hx => div_pos hx.1 (cosh_pos x)) ha'

theorem prefixSecondOrderProfile_strictMonoOn : StrictMonoOn prefixSecondOrderProfile (Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  exact prefixSecondOrderIntegral_strictMonoOn (by change 0 < 2*a; linarith [ha])
    (by change 0 < 2*b; linarith [hb]) (by linarith)

theorem prefixSecondOrderProfile_monotoneOn : MonotoneOn prefixSecondOrderProfile (Ioi 0) :=
  prefixSecondOrderProfile_strictMonoOn.monotoneOn

theorem prefixSecondOrderProfile_lt_pi_div_two {a : ℝ} (ha : 0 < a) :
    prefixSecondOrderProfile a < Real.pi/2 := by
  have hlt := prefixSecondOrderProfile_strictMonoOn ha (show 0 < a+1 by linarith)
    (show a < a+1 by linarith)
  have hle : prefixSecondOrderProfile (a+1) ≤ Real.pi/2 := by
    apply ge_of_tendsto prefixSecondOrderProfile_infinite
    filter_upwards [eventually_ge_atTop (a+1)] with b hb
    exact prefixSecondOrderProfile_monotoneOn (by change 0 < a+1; linarith)
      (by change 0 < b; linarith) hb
  exact hlt.trans_le hle

end
end chebyshev1.Nonlinear
