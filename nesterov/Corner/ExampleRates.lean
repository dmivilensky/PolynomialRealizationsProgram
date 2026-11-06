import nesterov.Corner.Example
import nesterov.Corner.Kappa

/-! The arithmetic gap in the source example bounds the actual rate
coefficients, with the exact lower and upper constants. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology

theorem corner_example_kappa_bounds
    (F : Scaling ℝ (𝓝[>] (0:ℝ)) 3 2 (1/2)) (he : F.epsilon=id)
    (ha : Tendsto F.cornerA (𝓝[>] (0:ℝ)) (𝓝 2))
    (hb : Tendsto F.cornerB (𝓝[>] (0:ℝ)) (𝓝 1)) :
    ((3*Real.sqrt 6-13/2:ℝ):EReal)≤
      liminf (fun κ=>(F.fullKappaCoefficient κ:EReal)) atTop ∧
    liminf (fun κ=>(F.fullKappaCoefficient κ:EReal)) atTop≤
      limsup (fun κ=>(F.restKappaCoefficient κ:EReal)) atTop ∧
    limsup (fun κ=>(F.restKappaCoefficient κ:EReal)) atTop≤((17/20:ℝ):EReal) := by
  have hpos : 0<Corner.cLag 3 2 1 := by
    rw [Corner.example_cLag]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
    have hr := Real.sqrt_nonneg (6:ℝ)
    nlinarith
  have hlow : 3*Real.sqrt 6-13/2≤(1:ℝ) := by
    have h := Corner.example_strict_gap
    rw [Corner.example_cLag,Corner.example_cDisc] at h
    linarith
  have h := F.corner_kappa_bounds he ha hb (by norm_num) hpos
  rw [show Flow.cQ 3 2=1 by norm_num [Flow.cQ],Corner.example_cLag,
    Corner.example_cDisc] at h
  have hlowE : ((3*Real.sqrt 6-13/2:ℝ):EReal)≤(1:EReal) :=
    EReal.coe_le_coe_iff.mpr hlow
  have hhiE : ((17/20:ℝ):EReal)≤(1:EReal) :=
    EReal.coe_le_coe_iff.mpr (by norm_num)
  simpa only [EReal.coe_one,min_eq_right hlowE,min_eq_right hhiE] using h

end
end nesterov.TwoStep.Scaling
