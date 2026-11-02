import jacobi.Support.TopUniformLimit
import jacobi.Analysis.HalfMeshCompactness

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The original uniform top-node limit includes the entire matrix half
chain 2*m<=n+1, where n is the polynomial degree and n+1 the matrix
dimension. In particular its genuine middle coordinate is retained.
Use: naturalWave_edge restores the original polynomial normalization on every index required by the full source Gram–Cholesky section, using the true n+1 matrix dimension.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual positive support ground polynomial has its uniform original top-profile limit through the entire matrix half chain, including the possible extra middle index.
Use: naturalWave_edge restores the original polynomial normalization on every index required by the full source Gram–Cholesky section, using the true n+1 matrix dimension.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the proved original moving-mesh limit covers every positive limiting ratio, and the original small-mesh bound covers zero. The top profile is continuous, so the actual mesh error vanishes along every cofinal moving half chain. The compact half-mesh criterion includes the true middle index and makes the convergence uniform. -/
theorem topValue_uniform_half {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→
      |(n:ℝ)^(-gamma a)*topValue a b ha hb n m-topProfile a b ((m:ℝ)/(n:ℝ))|<ε := by
  -- Use compactness on the entire original matrix half, including its middle index.
  have h := jacobi.Analysis.half_mesh_uniform_zero
    (fun n m => (n:ℝ)^(-gamma a)*topValue a b ha hb n m-topProfile a b ((m:ℝ)/(n:ℝ)))
  apply h
  intro ns ms t ht hn hm _hhalf
  have hu : Tendsto (fun i => (ns i:ℝ)^(-gamma a)*topValue a b ha hb (ns i) (ms i)) atTop
      (𝓝 (topProfile a b t)) := by
    by_cases ht0:t=0
    · subst t
      simpa only [topProfile_zero ha] using topValue_zero_limit ha hb hn hm
    · exact topValue_limit ha hb ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩ hn hm
  have hv := (topProfile_continuous (b:=b) ha).continuousAt.tendsto.comp hm
  simpa only [sub_self,Function.comp_def] using hu.sub hv

end
end jacobi.Support
