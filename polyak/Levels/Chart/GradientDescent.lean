import polyak.Levels.Chart.Coefficients
import polyak.General.Regions.GradientDescent

/-! The zero-momentum face of the coefficient chart. -/
namespace polyak.Levels.Chart
open General

theorem gradientDescent_chart (q : Tuning) (hβ : q.beta=0) :
    (coefficients q).c2=0 ∧ Regions.OmegaOne q :=
  ⟨(coefficient_quadratic_zero_iff q).mpr hβ,Regions.gradientDescent_mem_omegaOne q hβ⟩

end polyak.Levels.Chart
