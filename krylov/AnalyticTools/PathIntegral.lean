import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-!
Article: main_krylov, apC:prop:LV, analytic ODE background.
Use: integration of continuous paths on the unit interval as an actual bounded
linear operator. This is the linear part of the rescaled Picard equation.
Source: the fundamental theorem of calculus and the uniform integral bound.
-/

namespace krylov.AnalyticTools
noncomputable section
open Set MeasureTheory

abbrev PathDomain := Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Constant continuation past the two ends of a compact path. -/
def extendPath (f : C(PathDomain, E)) (t : ℝ) : E :=
  f (projIcc 0 1 (by norm_num) t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_extendPath (f : C(PathDomain, E)) : Continuous (extendPath f) :=
  f.continuous.comp continuous_projIcc

/-- The primitive is continuous in its endpoint, with the genuine integral. -/
def pathPrimitive (f : C(PathDomain, E)) : C(PathDomain, E) where
  toFun u := ∫ t in 0..(u : ℝ), extendPath f t
  continuous_toFun := by
    have h : Continuous (fun u : ℝ ↦ ∫ t in 0..u, extendPath f t) :=
      continuous_iff_continuousAt.mpr fun u ↦
        ((continuous_extendPath f).integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
    exact h.comp continuous_subtype_val

theorem norm_pathPrimitive_le (f : C(PathDomain, E)) : ‖pathPrimitive f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro u
  calc
    ‖pathPrimitive f u‖ ≤ ‖f‖ * |(u : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      exact f.norm_coe_le_norm _
    _ ≤ ‖f‖ := by
      rw [sub_zero, abs_of_nonneg u.2.1]
      exact mul_le_of_le_one_right (norm_nonneg _) u.2.2

/-- Compact-path integration is a continuous linear map with norm at most one. -/
def pathIntegralCLM : C(PathDomain, E) →L[ℝ] C(PathDomain, E) :=
  LinearMap.mkContinuous
    { toFun := pathPrimitive
      map_add' := by
        intro f g
        ext u
        exact intervalIntegral.integral_add
          ((continuous_extendPath f).intervalIntegrable _ _)
          ((continuous_extendPath g).intervalIntegrable _ _)
      map_smul' := by
        intro c f
        ext u
        exact intervalIntegral.integral_smul c (extendPath f) }
    1 (fun f ↦ by
      change ‖pathPrimitive f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_pathPrimitive_le f)

theorem pathIntegralCLM_apply (f : C(PathDomain, E)) (u : PathDomain) :
    pathIntegralCLM f u = ∫ t in 0..(u : ℝ), extendPath f t := rfl

end
end krylov.AnalyticTools
