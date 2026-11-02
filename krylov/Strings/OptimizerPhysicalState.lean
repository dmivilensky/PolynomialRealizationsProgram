import krylov.Strings.OptimizerQuadratures
import krylov.Strings.FeedbackSmoothBridge
import krylov.Strings.GlobalDensityMass

/-!
Article: main_krylov, thm:value, global physical feedback coordinates.
Use: invert the genuinely unbounded quadrature clock and derive the physical
string differential equations on the entire half-line. No global physical
solution is supplied as an optimizer hypothesis.
Source: the proved clock inverse theorem and ordinary derivative chain rules.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Actual LV time corresponding to physical length. -/
def inverseClock (s : ℝ → ℝ) : ℝ → ℝ := Function.invFun (physicalClock s)

/-- Physical position, obtained from its actual quadrature. -/
def physicalPosition (s : ℝ → ℝ) (x : ℝ) : ℝ := expPrimitive s (inverseClock s x)

/-- Physical slope, obtained from `dp/dτ=p`. -/
def physicalSlope (s : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (inverseClock s x)

/-- Physical energy, obtained from `dK/dτ=UK`. -/
def physicalEnergy (s U : ℝ → ℝ) (x : ℝ) : ℝ := expPrimitive U (inverseClock s x)

/-- Positive physical feedback density, computed from the constructed state. -/
def physicalDensity (s : ℝ → ℝ) (x : ℝ) : ℝ :=
  physicalSlope s x / (physicalPosition s x * Real.sqrt (s (inverseClock s x)))

/-- The inverse physical clock sends the source origin to initial LV time. -/
theorem inverseClock_zero {s : ℝ → ℝ} (hs : Continuous s) (hp : ∀ t, 0 < s t) :
    inverseClock s 0 = 0 := by
  simpa only [physicalClock_zero, inverseClock] using
    Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective (0 : ℝ)

/-- The physical position, slope and energy each start at one. -/
theorem physical_initial {s U : ℝ → ℝ} (hs : Continuous s) (hp : ∀ t, 0 < s t) :
    physicalPosition s 0 = 1 ∧ physicalSlope s 0 = 1 ∧ physicalEnergy s U 0 = 1 := by
  simp [physicalPosition, physicalSlope, physicalEnergy, inverseClock_zero hs hp]

/-- The genuine physical feedback density is strictly positive. -/
theorem physicalDensity_pos {s : ℝ → ℝ} (hp : ∀ t, 0 < s t) (x : ℝ) :
    0 < physicalDensity s x :=
  div_pos (Real.exp_pos _) (mul_pos (expPrimitive_pos _ _) (Real.sqrt_pos.mpr (hp _)))

/-- The actual quadrature position has the physical slope as its derivative. -/
theorem physicalPosition_derivative {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (physicalPosition s) (physicalSlope s x) x := by
  let t := inverseClock s x
  have hinv : HasDerivAt (inverseClock s) (physicalSpeed s t)⁻¹ x :=
    inverseClock_derivative_nonneg hs hp h₁ hx
  have hd : HasDerivAt (physicalPosition s)
      ((s t * expPrimitive s t) * (physicalSpeed s t)⁻¹) x :=
    (expPrimitive_derivative hs t).comp x hinv
  convert hd using 1
  dsimp [physicalSlope, physicalSpeed, t]
  field_simp [(hp (inverseClock s x)).ne', (expPrimitive_pos s (inverseClock s x)).ne']

/-- The actual slope has the mass-driven derivative selected by feedback. -/
theorem physicalSlope_derivative {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (physicalSlope s)
      (physicalPosition s x * physicalDensity s x ^ 2) x := by
  let t := inverseClock s x
  have hinv : HasDerivAt (inverseClock s) (physicalSpeed s t)⁻¹ x :=
    inverseClock_derivative_nonneg hs hp h₁ hx
  have hd : HasDerivAt (physicalSlope s) (Real.exp t * (physicalSpeed s t)⁻¹) x :=
    (Real.hasDerivAt_exp t).comp x hinv
  convert hd using 1
  dsimp [physicalPosition, physicalSlope, physicalDensity, physicalSpeed, t]
  have hsqrt := Real.sq_sqrt (hp (inverseClock s x)).le
  field_simp
  rw [hsqrt]

/-- The energy derivative follows from the proved LV/physical ratio identity. -/
theorem physicalEnergy_derivative {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (physicalEnergy s U)
      (physicalPosition s x ^ 2 * physicalDensity s x ^ 2) x := by
  let t := inverseClock s x
  have hinv : HasDerivAt (inverseClock s) (physicalSpeed s t)⁻¹ x :=
    inverseClock_derivative_nonneg hs hp h₁ hx
  have ht : 0 ≤ t := inverseClock_nonneg hs hp h₁ hx
  have hr := coordinate_ratio hs hU hU₀ hode ht
  have hd : HasDerivAt (physicalEnergy s U)
      ((U t * expPrimitive U t) * (physicalSpeed s t)⁻¹) x :=
    (expPrimitive_derivative hU t).comp x hinv
  convert hd using 1
  dsimp [physicalPosition, physicalSlope, physicalDensity, physicalSpeed]
  dsimp [stateRatio] at hr
  have hsqrt := Real.sq_sqrt (hp t).le
  have hK := (expPrimitive_pos U t).ne'
  have hφ := (expPrimitive_pos s t).ne'
  have hspos := (hp t).ne'
  change (expPrimitive s t) ^ 2 *
      (Real.exp t / (expPrimitive s t * Real.sqrt (s t))) ^ 2 =
    U t * expPrimitive U t * (expPrimitive s t * s t / Real.exp t)⁻¹
  rw [hr]
  field_simp
  rw [hsqrt, div_self hspos]

/-- The constructed global physical path is a genuine smooth string at every
nonnegative position. All differential equations are derived from the clock
and quadratures, rather than included as assumptions on a global optimizer. -/
theorem physical_smoothStringAt {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    krylov.ContinuumControl.SmoothStringAt (physicalPosition s) (physicalSlope s)
      (physicalEnergy s U) (physicalDensity s) x :=
  ⟨expPrimitive_pos _ _, Real.exp_pos _, expPrimitive_pos _ _,
    physicalPosition_derivative hs hp h₁ hx, physicalSlope_derivative hs hp h₁ hx,
    physicalEnergy_derivative hs hU hp h₁ hU₀ hode hx⟩

end
end krylov.Strings.OptimizerQuadratures
