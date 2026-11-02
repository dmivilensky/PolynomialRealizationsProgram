import jacobi.Analysis.UniformMeshSquares
import jacobi.Support.TopNorming

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The full actual top-node polynomial squared norm converges to the
literal printed Gamma amplitude times the original reference norm.
The final finite endpoint term is included explicitly.
Use: topWeight_limit obtains the genuine original top spectral probability from the proved complete Christoffel normalization.
-/
namespace jacobi.Support
noncomputable section
open Real Filter MeasureTheory jacobi.Reference jacobi.Analysis
open scoped Topology

/-- The actual full top-node polynomial squared norm has the exact positive printed continuum norming limit.
Use: topWeight_limit obtains the genuine original top spectral probability from the proved complete Christoffel normalization.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the genuine full-chain uniform limit gives the squared Riemann-sum limit by the shared mesh theorem. The exact final coordinate contributes its squared scaled value divided by n; full-chain convergence at the endpoint makes this term tend to zero. The original integral has already been identified with the printed reference norm. -/
theorem topValue_square_norm_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ =>
      (∑j∈Finset.range (n+1),((n:ℝ)^(-gamma a)*topValue a b ha hb n j)^2)/(n:ℝ)) atTop
      (𝓝 (topAmplitudeSquare a b*norming a 0)) := by
  -- The full original finite norm includes its last coordinate, whose vanishing contribution is treated separately.
  have hmain := uniform_mesh_square_integral
    (fun n j => (n:ℝ)^(-gamma a)*topValue a b ha hb n j)
    (topProfile a b) (topProfile_continuous ha) (by
      intro ε hε
      obtain ⟨N,hN⟩ := topValue_full_uniform ha hb ε hε
      exact ⟨N,fun n hn j hj => hN n hn j hj.le⟩)
  have hend : Tendsto (fun n:ℕ => (n:ℝ)^(-gamma a)*topValue a b ha hb n n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := topValue_full_uniform ha hb ε hε
    filter_upwards [eventually_ge_atTop N,eventually_gt_atTop (0:ℕ)] with n hn hnpos
    have h := hN n hn n le_rfl
    have hnr : (n:ℝ)≠0 := by exact_mod_cast hnpos.ne'
    simpa only [div_self hnr,topProfile,mul_one,sin_pi,
      Real.zero_rpow (parameter_pos ha hb).1.ne',mul_zero,sub_zero,Real.dist_eq] using h
  have htail := (hend.pow 2).mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))
  have h := hmain.add htail
  rw [topProfile_norming ha hb] at h
  simpa only [Finset.sum_range_succ,add_div,mul_one_div,zero_pow (by decide : 2≠0),zero_mul,add_zero] using h

end
end jacobi.Support
