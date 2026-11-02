import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
Article: jacobi, Proposition B.1.
A common interface records genuine classical restoring solutions and their
actual first derivatives on a specified interval. It contains no phase or
asymptotic hypothesis. The actual Bessel and finite Jacobi solutions instantiate
it from their previously proved equations and simple-zero theorems.
Source: the classical amplitude/phase transformation for a nontrivial real second-order ODE.
Use: the same rigorously constructed Pruefer phase applies to the original Bessel and Jacobi equations.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set MeasureTheory

/-- An actual nontrivial classical restoring solution on a specified physical domain.
Use: the same rigorously constructed Pruefer phase applies to the original Bessel and Jacobi equations.
Article: jacobi, Proposition B.1.
-/
structure RestoringSolution (I : Set ℝ) where
  /-- The actual real solution value used in the source differential equation. -/
  value : ℝ → ℝ
  /-- Its actual ordinary derivative, independently specified for exact differentiation. -/
  slope : ℝ → ℝ
  /-- The actual restoring coefficient in the original equation. -/
  potential : ℝ → ℝ
  /-- Global measurability of the original solution, for its literal phase integrals. -/
  value_measurable : Measurable value
  /-- Global measurability of the original slope, for its literal phase integrals. -/
  slope_measurable : Measurable slope
  /-- Global measurability of the actual restoring coefficient. -/
  potential_measurable : Measurable potential
  /-- Continuity of the actual restoring coefficient at every physical interior point. -/
  potential_continuous : ∀ x∈I,ContinuousAt potential x
  /-- The given slope is genuinely the ordinary derivative of the original solution. -/
  first : ∀ x∈I,HasDerivAt value (slope x) x
  /-- The original slope satisfies the true second-order restoring equation. -/
  second : ∀ x∈I,HasDerivAt slope (-potential x*value x) x
  /-- The original state never has both coordinates zero; no phase property is postulated. -/
  nontrivial : ∀ x∈I,value x≠0 ∨ slope x≠0

namespace RestoringSolution
variable {I : Set ℝ} (S : RestoringSolution I)

/-- The actual Euclidean squared length of the original value/slope state.
Use: its strict positivity makes every normalized phase coordinate legitimate.
Article: jacobi, Proposition B.1.
-/
def energy (x : ℝ) : ℝ := S.value x^2+S.slope x^2

/-- The actual positive Euclidean amplitude of the original state.
Use: normalizes the genuine two-dimensional restoring state to the unit circle.
Article: jacobi, Proposition B.1.
-/
def amplitude (x : ℝ) : ℝ := √(S.energy x)

/-- The genuine amplitude is strictly positive at every physical point.
Use: excludes division by zero in every actual phase calculation.
Article: jacobi, Proposition B.1.
Proof: one of the original state coordinates is nonzero, so its square is strictly positive and the other square is nonnegative. -/
theorem energy_pos {x : ℝ} (hx : x∈I) : 0<S.energy x := by
  rcases S.nontrivial x hx with hf | hg
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hf) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hg)

/-- The genuine amplitude is strictly positive throughout the physical domain.
Use: the real square-root branch in the actual phase construction is uniquely fixed.
Article: jacobi, Proposition B.1.
Proof: the actual energy is positive and so is its positive square root. -/
theorem amplitude_pos {x : ℝ} (hx : x∈I) : 0<S.amplitude x := Real.sqrt_pos.mpr (S.energy_pos hx)

/-- The square of the actual amplitude is exactly the actual original state energy.
Use: every phase algebra identity is proved from the original state coordinates.
Article: jacobi, Proposition B.1.
Proof: the proved positive energy justifies the squared-square-root identity. -/
theorem amplitude_sq {x : ℝ} (hx : x∈I) : S.amplitude x^2=S.value x^2+S.slope x^2 :=
  Real.sq_sqrt (S.energy_pos hx).le

/-- The exact ordinary derivative of the original state energy.
Use: differentiates the genuine amplitude without assuming a phase equation.
Article: jacobi, Proposition B.1.
Proof: differentiate both original squared coordinates and substitute the actual restoring derivative. -/
theorem energy_hasDerivAt {x : ℝ} (hx : x∈I) :
    HasDerivAt S.energy (2*(1-S.potential x)*S.value x*S.slope x) x := by
  convert ((S.first x hx).pow 2).add ((S.second x hx).pow 2) using 1
  · rfl
  · norm_num only [Nat.reduceSub,Nat.cast_ofNat,pow_one]
    ring

/-- The exact actual ordinary derivative of the original positive amplitude.
Use: derives the genuine normalized state rotation before constructing a continuous phase.
Article: jacobi, Proposition B.1.
Proof: compose the actual energy derivative with the true positive square-root derivative and collect the nonzero amplitude factor. -/
theorem amplitude_hasDerivAt {x : ℝ} (hx : x∈I) :
    HasDerivAt S.amplitude ((1-S.potential x)*S.value x*S.slope x/S.amplitude x) x := by
  convert (Real.hasDerivAt_sqrt (S.energy_pos hx).ne').comp x (S.energy_hasDerivAt hx) using 1
  · rfl
  · dsimp [amplitude]
    ring

end RestoringSolution
end
end jacobi.Oscillation
