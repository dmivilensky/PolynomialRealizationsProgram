import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Article: Appendix C, quadratic remainders of the analytic actual rate.
Use: convert analyticity and a proved first derivative into the printed O(x²) statement.
-/

namespace polyak.Asymptotics
noncomputable section
open Filter
open scoped Topology

/-- Article: the first-order Taylor formula with an ordinary quadratic big-O remainder. -/
theorem analytic_first_order {f : ℝ → ℝ} {x d : ℝ}
    (hf : AnalyticAt ℝ f x) (hd : HasDerivAt f d x) :
    (fun y : ℝ => f y-f x-d*(y-x))=O[𝓝 x] (fun y => (y-x)^2) := by
  obtain ⟨p,hp⟩ := hf
  have hcoeff : p 1 (fun _ => (1 : ℝ))=d := hp.hasDerivAt.unique hd
  have hlin (y : ℝ) : p 1 (fun _ => y)=d*y := by
    have hh := (p 1).map_smul_univ (fun _ => y) (fun _ => (1 : ℝ))
    simpa only [smul_eq_mul,mul_one,Fin.prod_univ_one,hcoeff,mul_comm] using hh
  have hpartial (y : ℝ) : p.partialSum 2 y=f x+d*y := by
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,Finset.sum_range_zero,
      zero_add,hp.coeff_zero,hlin]
  have ho := hp.isBigO_sub_partialSum_pow 2
  have ht : Tendsto (fun y : ℝ => y-x) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => y-x) := by fun_prop
    simpa only [sub_self] using hc.continuousAt.tendsto (x:=x)
  have hh := ho.comp_tendsto ht
  simpa only [Function.comp_def,hpartial,add_sub_cancel,sub_add_cancel,
    Real.norm_eq_abs,sq_abs,sub_sub] using hh

end
end polyak.Asymptotics
