import polyak.Global.Circle.Probability
import polyak.Levels.Program.Normalization

/-! Normalize an actual strict finite-measure solution and symmetrize it
without losing a single signed lag or the positive minimizer moment. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.Levels MeasureTheory

theorem strict_solution_circle_probability {Θ:Curve} {w:Measure Frequency}
    (hw:ProgramSolution Θ nonzeroLags w)
    (hmin:0<∫ω,Θ.minimizer ω∂w)
    (hlag:∀n:ℤ,n≠0→0<∫ω,Θ.lag n ω∂w) :
    ∃μ:ProbabilityMeasure Circle,Circle.Symmetric (μ:Measure Circle) ∧
      (0<∫x,Circle.minimizer Θ x∂(μ:Measure Circle)) ∧
      ∀n:ℤ,n≠0→0<∫x,Circle.lag Θ n x∂(μ:Measure Circle) := by
  let wf:FiniteMeasure Frequency:=⟨w,hw.1⟩
  have hwf:wf≠0 := by
    intro he
    exact hw.2.1 (congrArg FiniteMeasure.toMeasure he)
  have hm : 0<(wf.mass:ℝ):=NNReal.coe_pos.mpr
    (pos_iff_ne_zero.mpr ((FiniteMeasure.mass_nonzero_iff wf).mpr hwf))
  let ν:ProbabilityMeasure Frequency:=wf.normalize
  let μ:ProbabilityMeasure Circle:=⟨Circle.symmetrize (ν:Measure Frequency),inferInstance⟩
  refine ⟨μ,Circle.reflect_symmetrize _,?_,?_⟩
  · change 0<Circle.cZero Θ (Circle.symmetrize (ν:Measure Frequency))
    rw [Circle.cZero_symmetrize]
    change 0<∫ω,Θ.minimizer ω∂wf.normalize
    rw [integral_finiteMeasure_normalize wf hwf]
    exact mul_pos (inv_pos.mpr hm) hmin
  · intro n hn
    change 0<Circle.moment Θ (Circle.symmetrize (ν:Measure Frequency)) n
    rw [Circle.moment_symmetrize]
    change 0<∫ω,Θ.lag n ω∂wf.normalize
    rw [integral_finiteMeasure_normalize wf hwf]
    exact mul_pos (inv_pos.mpr hm) (hlag n hn)

end polyak.Global.Sampling
