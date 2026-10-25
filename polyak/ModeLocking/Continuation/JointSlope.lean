import polyak.ModeLocking.Continuation.Kernels
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! An analytic slope in the original source coordinates, including the
frequency endpoints, obtained by differentiating the common joint extension. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General Levels

def jointLag (n : ℤ) (p : Chart.AmbientPoint) : ℝ :=
  Real.cos (Geometry.jointAngle p) - Real.cos ((n : ℝ) * p 4 - Geometry.jointAngle p)

def frequencyDirection : Chart.AmbientPoint := Pi.single 4 1

def jointSlope (n : ℤ) (p : Chart.AmbientPoint) : ℝ :=
  fderiv ℝ (jointLag n) p frequencyDirection

theorem analyticAt_jointLag (q : Tuning) (s : ℝ) (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) :
    AnalyticAt ℝ (jointLag n) ![q.kappa, q.y, q.beta, s, x] := by
  have ht := Geometry.analyticAt_jointAngle_actual q s hx
  exact (Real.analyticAt_cos.comp ht).sub (Real.analyticAt_cos.comp
    ((analyticAt_const.mul (Chart.analyticAt_coordinate _ 4)).sub ht))

theorem analyticAt_jointSlope (q : Tuning) (s : ℝ) (n : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 Real.pi) :
    AnalyticAt ℝ (jointSlope n) ![q.kappa, q.y, q.beta, s, x] :=
  ((ContinuousLinearMap.apply ℝ ℝ frequencyDirection).analyticAt _).comp
    (analyticAt_jointLag q s n hx).fderiv

theorem jointSlope_actual (q : Tuning) (s : ℝ) (n : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 Real.pi) :
    jointSlope n ![q.kappa, q.y, q.beta, s, x] = deriv (lagExtension q s n) x := by
  have hp : HasDerivAt (fun y : ℝ => ![q.kappa, q.y, q.beta, s, y]) frequencyDirection x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [frequencyDirection, Pi.single_apply] using hasDerivAt_const x q.kappa
    · simpa [frequencyDirection, Pi.single_apply] using hasDerivAt_const x q.y
    · simpa [frequencyDirection, Pi.single_apply] using hasDerivAt_const x q.beta
    · simpa [frequencyDirection, Pi.single_apply] using hasDerivAt_const x s
    · simp only [frequencyDirection, Pi.single_apply]
      convert hasDerivAt_id x using 1 <;> rfl
  exact ((analyticAt_jointLag q s n hx).differentiableAt.hasFDerivAt.comp_hasDerivAt x hp).deriv.symm

end polyak.ModeLocking.Continuation
