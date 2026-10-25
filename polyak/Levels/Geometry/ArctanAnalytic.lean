import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Article: Appendix E, analytic continuation at the endpoints.
Real arctangent is analytic at every real argument: tangent is analytic
with nonzero derivative on its principal strip, and arctangent is its
actual local inverse. This supplies the analytic endpoint formula without
assuming analyticity from smoothness. -/

namespace polyak.Levels
noncomputable section
open Filter Set
open scoped Topology

theorem analyticAt_real_arctan (a : ℝ) : AnalyticAt ℝ Real.arctan a := by
  have hc : Real.cos (Real.arctan a)≠0:=(Real.cos_arctan_pos a).ne'
  have ht : AnalyticAt ℝ Real.tan (Real.arctan a) := by
    convert (Real.analyticAt_sin.div Real.analyticAt_cos hc) using 1
    funext x
    exact Real.tan_eq_sin_div_cos x
  have hder : deriv Real.tan (Real.arctan a)≠0 := by
    rw [Real.deriv_tan]
    exact one_div_ne_zero (pow_ne_zero _ hc)
  have hi : AnalyticAt ℝ (fun x : ℝ=>x) (Real.arctan a):=analyticAt_id
  have hcomp : AnalyticAt ℝ (Real.arctan ∘ Real.tan) (Real.arctan a) := by
    apply hi.congr
    filter_upwards [Ioo_mem_nhds (Real.arctan_mem_Ioo a).1 (Real.arctan_mem_Ioo a).2] with x hx
    exact (Real.arctan_tan hx.1 hx.2).symm
  have hiff:=analyticAt_comp_iff_of_deriv_ne_zero (g:=Real.arctan) ht hder
  simpa only [Real.tan_arctan] using hiff.mp hcomp

end
end polyak.Levels
