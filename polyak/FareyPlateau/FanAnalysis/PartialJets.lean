import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The frequency-direction first and second jets of a jointly analytic
family are jointly continuous and equal the actual one-variable derivatives. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def partialFirst (F : E×ℝ→ℝ) (x : E×ℝ) : ℝ := fderiv ℝ F x (0,1)
def partialSecond (F : E×ℝ→ℝ) (x : E×ℝ) : ℝ := fderiv ℝ (partialFirst F) x (0,1)

theorem analyticAt_partialFirst {F : E×ℝ→ℝ} {x : E×ℝ} (hF : AnalyticAt ℝ F x) :
    AnalyticAt ℝ (partialFirst F) x := by
  exact ((ContinuousLinearMap.apply ℝ ℝ ((0,1) : E×ℝ)).analyticAt _).comp hF.fderiv

theorem analyticAt_partialSecond {F : E×ℝ→ℝ} {x : E×ℝ} (hF : AnalyticAt ℝ F x) :
    AnalyticAt ℝ (partialSecond F) x :=
  ((ContinuousLinearMap.apply ℝ ℝ ((0,1) : E×ℝ)).analyticAt _).comp
    (analyticAt_partialFirst hF).fderiv

theorem partialFirst_eq_deriv {F : E×ℝ→ℝ} {p : E} {δ : ℝ}
    (hF : DifferentiableAt ℝ F (p,δ)) :
    partialFirst F (p,δ)=deriv (fun t=>F (p,t)) δ := by
  have hp : HasDerivAt (fun t : ℝ=>(p,t)) (0,1) δ :=
    (hasDerivAt_const δ p).prodMk (hasDerivAt_id δ)
  exact (hF.hasFDerivAt.comp_hasDerivAt δ hp).deriv.symm

theorem partialSecond_eq_deriv {F : E×ℝ→ℝ} {p : E} {δ : ℝ}
    (hF : AnalyticAt ℝ F (p,δ)) :
    partialSecond F (p,δ)=deriv^[2] (fun t=>F (p,t)) δ := by
  have he : (fun t=>partialFirst F (p,t)) =ᶠ[nhds δ]
      deriv (fun t=>F (p,t)) := by
    have hp : ContinuousAt (fun t : ℝ=>(p,t)) δ := by fun_prop
    filter_upwards [hp.eventually hF.eventually_analyticAt] with t ht
    exact partialFirst_eq_deriv ht.differentiableAt
  change partialSecond F (p,δ)=deriv (deriv (fun t=>F (p,t))) δ
  change partialFirst (partialFirst F) (p,δ)=_
  rw [partialFirst_eq_deriv (analyticAt_partialFirst hF).differentiableAt]
  exact he.deriv_eq

theorem continuousAt_partialFirst {F : E×ℝ→ℝ} {x : E×ℝ} (hF : AnalyticAt ℝ F x) :
    ContinuousAt (partialFirst F) x := (analyticAt_partialFirst hF).continuousAt

theorem continuousAt_partialSecond {F : E×ℝ→ℝ} {x : E×ℝ} (hF : AnalyticAt ℝ F x) :
    ContinuousAt (partialSecond F) x := (analyticAt_partialSecond hF).continuousAt

end polyak.FareyPlateau.FanAnalysis
