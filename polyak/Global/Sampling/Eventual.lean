import polyak.Global.Sampling.Smoothing
import polyak.Global.Sampling.StrictNormalization
import polyak.Global.Sampling.Approximation
import polyak.Global.Sampling.AliasingProduct
import polyak.Global.Circle.SmoothConvolution

/-! The source sampling lemma and its full strict-solution corollary.
All kernel, density, Fourier-decay, and aliasing hypotheses are discharged. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels MeasureTheory

theorem eventually_periodic_of_circle_nondegenerate (q:Tuning) (s:ℝ)
    (μ:Measure Circle) [IsProbabilityMeasure μ] {M1 M2:ℝ} (hM1:0≤M1) (hM2:0≤M2)
    (hd:∀x,|phaseDerivative q s x|≤M1)
    (ht:∀v t,|phase q s (v+t)-phase q s v-phaseDerivative q s v*t|≤M2*t^2/2)
    (hmin:0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hlag:∀n:ℤ,0≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ)
    (hstrict:∀n∈lowLagSet (lagCutoff
      (Kernels.gainConstant*(∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ))
      (6*M1*Kernels.mPhi) (8*M1^2*Kernels.mPhi+M2*Kernels.mK)),
        0<∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ) :
    ∃L0:ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q s) L := by
  obtain ⟨ε,δ,hε,hεπ,hδ,hminε,hmargin⟩:=
    shifted_smoothed_uniform_margin q s μ hM1 hM2 hd ht hmin hlag hstrict
  let f:C(Circle,ℝ):=⟨Circle.smoothDensity ε μ,Circle.continuous_smoothDensity hε μ⟩
  exact eventually_periodic_of_uniform_margin q s f (Circle.smoothDensity_nonneg hε μ)
    (Circle.smoothMeasure ε μ) (Circle.smoothDensity_measure hε hεπ μ) hδ hminε hmargin
    (densityPhase_fourier_decay q s f (Circle.smooth_smoothDensity hε μ))

theorem eventually_periodic_of_strict_probability (q:Tuning) (s:ℝ)
    (μ:Measure Circle) [IsProbabilityMeasure μ]
    (hmin:0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hlag:∀n:ℤ,n≠0→0<∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ) :
    ∃L0:ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q s) L := by
  obtain ⟨M1,M2,hM1,hM2,hd,ht⟩:=phase_uniform_taylor q s
  apply eventually_periodic_of_circle_nondegenerate q s μ hM1 hM2 hd ht hmin
  · intro n
    by_cases hn:n=0
    · subst n
      simp only [Circle.lag,Curve.lag_zero,integral_zero,le_refl]
    · exact (hlag n hn).le
  · intro n hn
    exact hlag n hn.1

theorem eventually_periodic_of_strict_solution (q:Tuning) (s:ℝ) {w:Measure Frequency}
    (hw:ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w)
    (hmin:0<∫ω,(Geometry.shiftedCurve q s).minimizer ω∂w)
    (hlag:∀n:ℤ,n≠0→0<∫ω,(Geometry.shiftedCurve q s).lag n ω∂w) :
    ∃L0:ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q s) L := by
  obtain ⟨μ,_hsym,hminμ,hlagμ⟩:=strict_solution_circle_probability hw hmin hlag
  exact eventually_periodic_of_strict_probability q s (μ:Measure Circle) hminμ hlagμ

end polyak.Global.Sampling
