import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import jacobi.Analysis.DimensionRatio
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Convergence along every moving half-chain mesh implies uniform
convergence over that whole mesh. The only compactness used is that
of the actual closed spatial half interval, including its zero end.
Source: the subsequence criterion for uniform convergence on a compact set.
Use: the actual normalized Volterra residual vanishes along moving mesh points by finiteGroundMesh_limit, so its error is uniformly small before discrete Gronwall is applied to the original complex support polynomials.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter
open scoped Topology

/-- Vanishing along every cofinal moving physical half mesh implies uniform vanishing on the entire actual half mesh.
Use: the actual normalized Volterra residual vanishes along moving mesh points by finiteGroundMesh_limit, so its error is uniformly small before discrete Gronwall is applied to the original complex support polynomials.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: compactness of the closed interval [0,1/2].
Proof: a failure of uniformity selects bad original mesh values at cofinally increasing degrees. The corresponding ratios have a convergent subsequence in the actual closed half interval. The assumed moving-mesh convergence forces those same bad errors to zero, a contradiction. -/
theorem half_mesh_uniform_zero {E:Type*} [NormedAddCommGroup E] (f:ℕ→ℕ→E)
    (hf:∀n m:ℕ→ℕ,∀t∈Icc (0:ℝ) (1/2),Tendsto n atTop atTop→
      Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop (𝓝 t)→
      (∀i,2*m i≤n i+1)→Tendsto (fun i => f (n i) (m i)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→‖f n m‖<ε := by
  -- Choose actual bad mesh points if uniform convergence fails.
  classical
  intro ε hε
  by_contra h
  push Not at h
  choose ns hns ms hmesh hbad using h
  have hnT : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hratios (i:ℕ) : (ms i:ℝ)/((ns i:ℝ)+1)∈Icc (0:ℝ) (1/2) := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (by positivity),?_⟩
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(ns i:ℝ)+1)).mpr
    have hmr : 2*(ms i:ℝ)≤(ns i:ℝ)+1 := by exact_mod_cast hmesh i
    linarith
  obtain ⟨t,ht,φ,hφ,hratio⟩ := isCompact_Icc.tendsto_subseq hratios
  -- Compactness uses the matrix dimension; convert its ratio back to the original degree.
  have hnT' := hnT.comp hφ.tendsto_atTop
  have hratio' : Tendsto (fun i => (ms (φ i):ℝ)/(ns (φ i):ℝ)) atTop (𝓝 t) := by
    exact size_to_degree_mesh (m:=ms ∘ φ) hnT' hratio
  have hlim := hf (ns ∘ φ) (ms ∘ φ) t ht (hnT.comp hφ.tendsto_atTop)
    hratio' (fun i => hmesh (φ i))
  obtain ⟨i,hi⟩ := (hlim.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  exact (not_lt_of_ge (hbad (φ i))) hi

end
end jacobi.Analysis
