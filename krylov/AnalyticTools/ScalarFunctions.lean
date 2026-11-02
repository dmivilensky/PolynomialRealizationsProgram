import krylov.AnalyticTools.LocalInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, thm:value, analytic scalar coordinates.
Use: expose the positive real square root and a scalar analytic local inverse
through the existing power/logarithm and inverse-function APIs.
Source: mathlib real logarithm analyticity and analytic inverse power series.
-/

namespace krylov.AnalyticTools
noncomputable section
open Set Filter
open scoped Topology

/-- The positive square root of an actual analytic real curve is analytic
wherever its actual value is strictly positive. -/
theorem analyticAt_sqrt_comp {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hp : 0 < f x) :
    AnalyticAt ℝ (fun u ↦ Real.sqrt (f u)) x := by
  have ha : AnalyticAt ℝ (fun u ↦ Real.exp (Real.log (f u) * (1 / 2))) x :=
    ((hf.log hp).mul analyticAt_const).rexp'
  apply ha.congr
  filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hp)] with u hu
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu]

/-- A scalar analytic map with nonzero actual derivative has an actual
analytic local inverse with both germ identities. -/
theorem exists_analytic_scalar_inverse {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hd : deriv f x ≠ 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g (f x) ∧ g (f x) = x ∧
      (∀ᶠ t in 𝓝 x, g (f t) = t) ∧ (∀ᶠ u in 𝓝 (f x), f (g u) = u) := by
  let i : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (.mk0 (deriv f x) hd)
  apply exists_analytic_local_inverse hf i
  rw [hf.differentiableAt.hasDerivAt.hasFDerivAt.fderiv]
  apply ContinuousLinearMap.ext
  intro t
  convert! (ContinuousLinearEquiv.unitsEquivAut_apply (Units.mk0 (deriv f x) hd) t).symm using 1

end
end krylov.AnalyticTools
