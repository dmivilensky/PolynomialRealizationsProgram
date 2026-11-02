import jacobi.Analysis.UniformMeshIntegral

/-!
Article: jacobi, Theorem 2.1.
Uniform convergence of the actual polynomial mesh values implies
convergence of their squared mesh norms. All boundedness needed for
the passage to squares follows from compact continuity.
Source: uniform Riemann sums and the elementary difference of squares.
Use: uniform_mesh_square_integral and the support edge weight normalization pass from original polynomial limits to genuine squared spectral norms.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology

/-- Uniform convergence of actual finite mesh values implies uniform convergence of their squares.
Use: uniform_mesh_square_integral and the support edge weight normalization pass from original polynomial limits to genuine squared spectral norms.
Article: jacobi, Theorem 2.1.
Source: uniform continuity of squaring on bounded intervals.
Proof: compact continuity bounds the limit values by M. Choose a uniform error below both one and epsilon/(2*M+1), then factor the exact difference of squares and bound the sum factor by 2*M+1. -/
theorem uniform_mesh_squares (a : ℕ→ℕ→ℝ) (f : ℝ→ℝ) (hf:Continuous f)
    (ha:∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀j<n,|a n j-f ((j:ℝ)/(n:ℝ))|<ε) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀j<n,|(a n j)^2-(f ((j:ℝ)/(n:ℝ)))^2|<ε := by
  -- The original mesh values need no independent square-norm certificate: their uniform error supplies the required bounded interval.
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s:=Icc (0:ℝ) 1) hf.continuousOn
  let M := max C 0
  have hM : 0≤M := le_max_right _ _
  intro ε hε
  let δ := min 1 (ε/(2*M+1))
  have hδ : 0<δ := lt_min (by norm_num) (div_pos hε (by positivity))
  obtain ⟨N,hN⟩ := ha δ hδ
  refine ⟨max N 1,?_⟩
  intro n hn j hj
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have herr := hN n (by omega) j hj
  have hratio : (j:ℝ)/(n:ℝ)∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hn0).mpr ?_⟩
    exact_mod_cast hj.le
  have hfM : |f ((j:ℝ)/(n:ℝ))|≤M := (hC _ hratio).trans (le_max_left _ _)
  have hsum : |a n j+f ((j:ℝ)/(n:ℝ))|≤2*M+1 := by
    have h := abs_add_le (a n j-f ((j:ℝ)/(n:ℝ))) (2*f ((j:ℝ)/(n:ℝ)))
    rw [show a n j-f ((j:ℝ)/(n:ℝ))+2*f ((j:ℝ)/(n:ℝ))=a n j+f ((j:ℝ)/(n:ℝ)) by ring,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
    have hδ1 : δ≤1 := min_le_left _ _
    linarith
  calc
    _ = |a n j-f ((j:ℝ)/(n:ℝ))| * |a n j+f ((j:ℝ)/(n:ℝ))| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |a n j-f ((j:ℝ)/(n:ℝ))| *(2*M+1) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ < δ*(2*M+1) := mul_lt_mul_of_pos_right herr (by positivity)
    _ ≤ ε := (le_div_iff₀ (by positivity : 0<2*M+1)).mp (min_le_right _ _)

/-- Uniform convergence of actual polynomial mesh values implies convergence of their genuine squared finite norms to the continuous squared norm.
Use: Support.topValue_square_norm_limit computes the original positive top-node spectral weight from the full actual polynomial norm.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: uniform Riemann sums and continuity of squaring.
Proof: the proved uniform difference-of-squares estimate supplies the hypotheses of the exact mesh integral convergence theorem. -/
theorem uniform_mesh_square_integral (a : ℕ→ℕ→ℝ) (f : ℝ→ℝ) (hf:Continuous f)
    (ha:∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀j<n,|a n j-f ((j:ℝ)/(n:ℝ))|<ε) :
    Tendsto (fun n:ℕ => (∑j∈Finset.range n,(a n j)^2)/(n:ℝ)) atTop
      (𝓝 (∫t in (0:ℝ)..1,(f t)^2)) :=
  uniform_mesh_integral (fun n j => (a n j)^2) (fun t => (f t)^2) (hf.pow 2)
    (uniform_mesh_squares a f hf ha)

end
end jacobi.Analysis
