import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, thm:LB, uniform true critical branch.
Use: solve the scalar rank-one critical equation without assuming any
regularity of the observed-data-dependent cubic coefficients.
Source: the stable quadratic formula, including a zero quadratic term.
-/
namespace krylov.Functions
noncomputable section

/-- The small root written without division by the cubic parameter.
Article: main_krylov, thm:LB. -/
def rankOneCriticalRoot (A c : ℝ) : ℝ := -2*c/(1+Real.sqrt (1-2*A*c))

/-- The stable branch solves the actual scalar critical equation even
when its quadratic coefficient vanishes. Article: thm:LB. -/
theorem rankOneCriticalRoot_equation (A c : ℝ) (h : 0≤1-2*A*c) :
    A/2*(rankOneCriticalRoot A c)^2+rankOneCriticalRoot A c+c=0 := by
  have hd : 0<1+Real.sqrt (1-2*A*c) := by positivity
  have hs := Real.sq_sqrt h
  dsimp only [rankOneCriticalRoot]
  field_simp
  rw [show A*2*c=2*A*c by ring]
  nlinarith only [congrArg (fun z : ℝ=>c*z) hs]

/-- Its magnitude is controlled uniformly over every admissible cubic
coefficient. Article: main_krylov, thm:LB. -/
theorem rankOneCriticalRoot_bound (A c : ℝ) : |rankOneCriticalRoot A c|≤2*|c| := by
  have hd : 0≤1+Real.sqrt (1-2*A*c) := by positivity
  simp only [rankOneCriticalRoot,abs_div,abs_mul,abs_neg,abs_of_nonneg hd]
  norm_num only [abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
  exact div_le_self (by positivity) (by linarith [Real.sqrt_nonneg (1-2*A*c)])

end
end krylov.Functions
