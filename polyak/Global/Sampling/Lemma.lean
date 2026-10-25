import polyak.Global.Sampling.Eventual
import polyak.Global.Sampling.CanonicalBounds

/-! Appendix E's finite-order sampling criterion with the actual
canonical supremum constants and the exact larger-root cutoff. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels MeasureTheory

def sourceCutoff (q:Tuning) (s:ℝ) (μ:Measure Circle) : ℕ :=
  lagCutoff (Kernels.gainConstant*(∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ))
    (6*canonicalM1 q s*Kernels.mPhi)
    (8*(canonicalM1 q s)^2*Kernels.mPhi+canonicalM2 q s*Kernels.mK)

theorem sampling_lemma (q:Tuning) (s:ℝ) (μ:Measure Circle) [IsProbabilityMeasure μ]
    (hfeasible:∀n:ℤ,n≠0→0≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ)
    (hmin:0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hnondegenerate:∀n∈lowLagSet (sourceCutoff q s μ),
      0<∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ) :
    ∃L0:ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q s) L := by
  obtain ⟨hd,ht⟩:=canonical_phase_uniform_taylor q s
  apply eventually_periodic_of_circle_nondegenerate q s μ
    (canonicalM1_nonneg q s) (canonicalM2_nonneg q s) hd ht hmin
  · intro n
    by_cases hn:n=0
    · subst n
      simp only [Circle.lag,Curve.lag_zero,integral_zero,le_refl]
    · exact hfeasible n hn
  · exact hnondegenerate

end polyak.Global.Sampling
