import nesterov.Trace.Disk

/-! Convert a real conjugation-invariant circle average to the source upper
semicircle integral, retaining its exact normalization. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real intervalIntegral

theorem circleAverage_half_integral {f : ℂ→ℝ}
    (hc : ContinuousOn f (sphere (0:ℂ) 1))
    (he : ∀ z∈sphere (0:ℂ) 1,f (star z)=f z) :
    circleAverage f 0 1=(1/Real.pi)*∫ ω in (0:ℝ)..Real.pi,f (Complex.exp ((ω:ℂ)*Complex.I)) := by
  let g := fun ω : ℝ=>f (circleMap 0 1 ω)
  have hgc : Continuous g := hc.comp_continuous (by fun_prop) (fun ω=>by simp)
  have hge (ω : ℝ) : g (-ω)=g ω := by
    unfold g
    rw [←conj_circleMap_zero]
    exact he _ (by simp)
  have hn : (∫ ω in (-Real.pi)..0,g ω)=∫ ω in (0:ℝ)..Real.pi,g ω := by
    have hh := intervalIntegral.integral_comp_neg (f:=g) (a:=(0:ℝ)) (b:=Real.pi)
    simp only [neg_zero,hge] at hh
    exact hh.symm
  have hadd := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (hgc.intervalIntegrable (-Real.pi) 0)
    (hgc.intervalIntegrable 0 Real.pi)
  rw [hn] at hadd
  have hshift := circleAverage_eq_integral_add (f:=f) (c:=(0:ℂ)) (R:=(1:ℝ)) (-Real.pi)
  change circleAverage f 0 1=(2*Real.pi)⁻¹ • ∫ θ in (0:ℝ)..2*Real.pi,g (θ+ -Real.pi) at hshift
  rw [intervalIntegral.integral_comp_add_right] at hshift
  have hb : 2*Real.pi+ -Real.pi=Real.pi := by ring
  simp only [zero_add,hb,smul_eq_mul] at hshift
  change circleAverage f 0 1=(2*Real.pi)⁻¹*(∫ ω in (-Real.pi)..Real.pi,g ω) at hshift
  rw [hshift,←hadd]
  have hg (ω : ℝ) : g ω=f (Complex.exp ((ω:ℂ)*Complex.I)) := by simp [g,circleMap]
  simp_rw [hg]
  ring

end
end nesterov.Trace
