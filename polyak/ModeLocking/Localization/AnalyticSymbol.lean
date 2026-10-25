import polyak.ModeLocking.Localization.ShiftDerivative
import polyak.ModeLocking.Regular.Slackness
import polyak.ModeLocking.Regular.Endpoints

/-! A single analytic extension of every finite certificate symbol, on a
neighborhood of the entire closed source frequency interval. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

def extendedSymbol (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ x : ℝ) : ℝ := (∑ i, a i*lagExtension q s (n i) x) +
      γ*Real.cos (Geometry.jointAngle ![q.kappa,q.y,q.beta,s,x])

theorem extendedSymbol_actual (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ : ℝ) (ω : Frequency) : extendedSymbol q s n a γ ω = symbol q s n a γ ω := by
  unfold extendedSymbol symbol Curve.minimizer
  simp only [lagExtension_actual,Geometry.jointAngle_actual q s ω.property]
  rfl

theorem analyticAt_extendedSymbol (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ x : ℝ) (hx : x ∈ Icc 0 Real.pi) : AnalyticAt ℝ (extendedSymbol q s n a γ) x := by
  have hp : AnalyticAt ℝ (fun x : ℝ => ![q.kappa,q.y,q.beta,s,x]) x := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    all_goals first | exact analyticAt_const | exact analyticAt_id
  have hangle := (Geometry.analyticAt_jointAngle_actual q s hx).comp
    (f := fun x : ℝ => ![q.kappa,q.y,q.beta,s,x]) hp
  exact (Finset.analyticAt_fun_sum _ fun i _ =>
    analyticAt_const.mul (analyticAt_lagExtension q s (n i) hx)).add
      (analyticAt_const.mul (Real.analyticAt_cos.comp hangle))

theorem continuousOn_extendedSymbol_second (q : General.Tuning) (s : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) :
    ContinuousOn (iteratedDeriv 2 (extendedSymbol q s n a γ)) (Icc 0 Real.pi) := by
  intro x hx
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
    (analyticAt_extendedSymbol q s n a γ x hx).deriv.deriv.continuousAt.continuousWithinAt
      (s := Icc 0 Real.pi)

theorem extendedSymbol_deriv_zero (q : General.Tuning) (s : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) : deriv (extendedSymbol q s n a γ) 0 = 0 := by
  have hs : HasDerivAt (fun x => ∑ i, a i*lagExtension q s (n i) x) 0 0 := by
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      ((analyticAt_lagExtension q s (n i) ⟨le_rfl,Real.pi_pos.le⟩).differentiableAt.hasDerivAt).const_mul (a i))
    convert hh using 1
    simp only [lagExtension_deriv_zero,mul_zero,Finset.sum_const_zero]
  have hp : AnalyticAt ℝ (fun x : ℝ => ![q.kappa,q.y,q.beta,s,x]) 0 := by
    apply AnalyticAt.pi
    intro j
    fin_cases j
    all_goals first | exact analyticAt_const | exact analyticAt_id
  have hangle := (Geometry.analyticAt_jointAngle_actual q s ⟨le_rfl,Real.pi_pos.le⟩).comp
    (f := fun x : ℝ => ![q.kappa,q.y,q.beta,s,x]) hp
  change AnalyticAt ℝ (fun x : ℝ => Geometry.jointAngle ![q.kappa,q.y,q.beta,s,x]) 0 at hangle
  have hm := hangle.differentiableAt.hasDerivAt.cos.const_mul γ
  have hm' : HasDerivAt (fun x : ℝ => γ*Real.cos
      (Geometry.jointAngle ![q.kappa,q.y,q.beta,s,x])) 0 0 := by
    convert hm using 1
    simp only [Geometry.jointAngle_actual q s ⟨le_rfl,Real.pi_pos.le⟩,
      Geometry.shiftedAngle_zero,Real.sin_pi,mul_zero,zero_mul,neg_zero]
  have hh : HasDerivAt (extendedSymbol q s n a γ) 0 0 := by
    convert hs.add hm' using 1
    · funext x
      rfl
    · norm_num
  exact hh.deriv

end polyak.ModeLocking.Localization
