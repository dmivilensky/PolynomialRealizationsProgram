import polyak.Global.Sampling.PhaseCircle
import polyak.Global.Sampling.UniformMargin
import polyak.Global.Circle.Smoothing

/-! Source shifted curves satisfy the smoothing lemma with a single
strict margin for all nonzero lags at the exact quadratic cutoff. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels MeasureTheory

theorem shifted_smoothed_uniform_margin (q : Tuning) (s : ℝ) (μ : Measure Global.Circle)
    [IsProbabilityMeasure μ] {M1 M2:ℝ} (hM1:0≤M1) (hM2:0≤M2)
    (hd : ∀x,|phaseDerivative q s x|≤M1)
    (ht : ∀v t,|phase q s (v+t)-phase q s v-phaseDerivative q s v*t|≤M2*t^2/2)
    (hmin : 0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hlag : ∀n:ℤ,0≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ)
    (hstrict : ∀n∈lowLagSet (lagCutoff
      (Kernels.gainConstant*(∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ))
      (6*M1*Kernels.mPhi) (8*M1^2*Kernels.mPhi+M2*Kernels.mK)),
        0<∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ) :
    ∃ε δ:ℝ,0<ε ∧ ε<Real.pi ∧ 0<δ ∧
      (0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂Circle.smoothMeasure ε μ) ∧
      ∀n:ℤ,n≠0→δ≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂Circle.smoothMeasure ε μ := by
  apply uniform_margin_from_smoothing hmin hM1 (mul_nonneg hM2 Kernels.mK_nonneg)
    (fun n=>∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ)
    (fun ε n=>∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂Circle.smoothMeasure ε μ)
    (fun ε=>∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂Circle.smoothMeasure ε μ)
    hlag hstrict
  · intro ε _ _ n
    have hh:=Circle.smoothing_constraint (phase_periodic q s) (continuous_phase q s)
      (phaseDerivative q s) hM1 hd ht n ε μ
    simp only [phaseConstraint_actual,phaseMinimizer_actual] at hh
    exact hh
  · intro ε _ _
    have hh:=Circle.smoothing_minimizer (phase_periodic q s) (continuous_phase q s)
      (phaseDerivative q s) hd ht ε μ
    simp only [phaseMinimizer_actual] at hh
    exact hh

theorem shifted_smoothed_margin_of_strict (q : Tuning) (s : ℝ) (μ : Measure Global.Circle)
    [IsProbabilityMeasure μ]
    (hmin : 0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hlag : ∀n:ℤ,n≠0→0<∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ) :
    ∃ε δ:ℝ,0<ε ∧ ε<Real.pi ∧ 0<δ ∧
      (0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂Circle.smoothMeasure ε μ) ∧
      ∀n:ℤ,n≠0→δ≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂Circle.smoothMeasure ε μ := by
  obtain ⟨M1,M2,hM1,hM2,hd,ht⟩:=phase_uniform_taylor q s
  apply shifted_smoothed_uniform_margin q s μ hM1 hM2 hd ht hmin
  · intro n
    by_cases hn:n=0
    · subst n
      simp only [Circle.lag,Curve.lag_zero,integral_zero,le_refl]
    · exact (hlag n hn).le
  · intro n hn
    exact hlag n hn.1

end polyak.Global.Sampling
