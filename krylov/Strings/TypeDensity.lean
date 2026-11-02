import krylov.Strings.Mass
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: main_krylov, s3:def:string, dM = varsigma² dx + dM_s.
Use: obtain the physical type density from the actual Radon–Nikodym derivative,
rather than assuming a supplied decomposition of the mass. The singular part
includes the distinguished origin atom; the state already accounts for that atom.
Source: mathlib's Lebesgue decomposition and almost-everywhere finiteness of rnDeriv.
-/

namespace krylov.Strings
noncomputable section
open MeasureTheory

namespace Mass

/-- The nonnegative square-root density defining the string's type clock. -/
def typeDensity (M : Mass) (x : ℝ) : ℝ :=
  Real.sqrt ((M.measure.rnDeriv volume x).toReal)

/-- Nonnegativity is pointwise, including the harmless chosen values on
exceptional null sets of the Radon–Nikodym derivative. -/
theorem typeDensity_nonneg (M : Mass) (x : ℝ) : 0 ≤ M.typeDensity x :=
  Real.sqrt_nonneg _

/-- The actual type density is measurable. -/
theorem measurable_typeDensity (M : Mass) : Measurable M.typeDensity :=
  Real.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- Squaring the chosen density recovers the Radon–Nikodym derivative
almost everywhere; infinity cannot be silently converted to a real density. -/
theorem typeDensity_sq_ae (M : Mass) :
    (fun x ↦ ENNReal.ofReal (M.typeDensity x ^ 2)) =ᵐ[volume] M.measure.rnDeriv volume := by
  have : IsLocallyFiniteMeasure M.measure := by
    dsimp [measure]
    infer_instance
  filter_upwards [Measure.rnDeriv_lt_top M.measure volume] with x hx
  rw [typeDensity, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

/-- The complete actual mass decomposition, valid with atoms and singular
continuous mass. No absolute continuity premise is imposed. -/
theorem type_mass_decomposition (M : Mass) :
    volume.withDensity (fun x ↦ ENNReal.ofReal (M.typeDensity x ^ 2)) +
      M.measure.singularPart volume = M.measure := by
  have : IsLocallyFiniteMeasure M.measure := by
    dsimp [measure]
    infer_instance
  rw [withDensity_congr_ae M.typeDensity_sq_ae]
  exact Measure.rnDeriv_add_singularPart _ _

end Mass
end
end krylov.Strings
