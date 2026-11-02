import jacobi.Analysis.DimensionRatio
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Article: jacobi, Theorem 2.1.
Convergence along every cofinal moving pair of physical matrix indices
implies uniform convergence on the complete finite half square.
Compactness uses the true matrix-size coordinates, so the middle row
and both singular endpoint edges are retained exactly.
Source: compactness of a closed rectangle and the subsequence criterion.
Use: matrixMesh_mem_half and gramKernelError use this same coordinate in the full uniform Gram limit and the ensuing finite-section coercivity argument.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter
open scoped Topology

/-- The physical coordinate of an actual finite matrix index, using its true n+1 dimension.
Use: matrixMesh_mem_half and gramKernelError use this same coordinate in the full uniform Gram limit and the ensuing finite-section coercivity argument.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def matrixMesh (n:ℕ) (i:Fin (n+1)) : ℝ := (i.val:ℝ)/((n:ℝ)+1)

/-- Every original matrix half-chain index lies in the exact closed physical half interval.
Use: the compact matrix error criterion and the actual continuous GL kernel limits apply on their original closed half square, including zero and the midpoint.
Article: jacobi, Proposition C.3.
Proof: the genuine positive matrix dimension preserves the defining integer half-index inequality under division. -/
theorem matrixMesh_mem_half {n:ℕ} {i:Fin (n+1)} (hi:2*i.val≤n+1) :
    matrixMesh n i∈Icc (0:ℝ) (1/2) := by
  refine ⟨by unfold matrixMesh; positivity,?_⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
  have : 2*(i.val:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hi
  linarith

/-- Every moving-pair error limit on cofinal actual matrix dimensions gives uniform vanishing on the entire actual physical half square.
Use: gramPerturbation_uniform turns the genuine complete two-edge spectral limit into the full uniform matrix-kernel approximation needed for finite-section coercivity and Gram–Cholesky convergence.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Source: sequential compactness of [0,1/2]^2.
Proof: a failure of uniformity selects original bad row-column pairs at cofinally large original dimensions. Their true matrix-size coordinates lie in the compact physical square and have a common convergent subsequence. Both original degree coordinates have the same limits. The assumed actual moving-pair limit then forces those same bad errors to zero. -/
theorem half_matrix_uniform_zero {E:Type*} [NormedAddCommGroup E]
    (f:∀n:ℕ,Fin (n+1)→Fin (n+1)→E)
    (hf:∀(ns:ℕ→ℕ),Tendsto ns atTop atTop→∀(i j:∀n:ℕ,Fin (ns n+1)),
      (∀n,2*(i n).val≤ns n+1)→(∀n,2*(j n).val≤ns n+1)→
      ∀t∈Icc (0:ℝ) (1/2),∀s∈Icc (0:ℝ) (1/2),
      Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t)→
      Tendsto (fun n:ℕ => ((j n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 s)→
      Tendsto (fun n => f (ns n) (i n) (j n)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i j:Fin (n+1),2*i.val≤n+1→2*j.val≤n+1→‖f n i j‖<ε := by
  -- A putative bad entry retains both of its actual dependent finite indices.
  classical
  intro ε hε
  by_contra h
  push Not at h
  choose ns hns is js hi hj hbad using h
  have hn : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hpair (n:ℕ) : (((is n).val:ℝ)/((ns n:ℝ)+1),((js n).val:ℝ)/((ns n:ℝ)+1))∈
      Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2) := ⟨matrixMesh_mem_half (hi n),matrixMesh_mem_half (hj n)⟩
  obtain ⟨p,hp,φ,hφ,hratio⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hpair
  -- Compactness of the true matrix square also supplies the original degree-mesh limits.
  have hnc := hn.comp hφ.tendsto_atTop
  have hiSize : Tendsto (fun n => ((is (φ n)).val:ℝ)/((ns (φ n):ℝ)+1)) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hratio
  have hjSize : Tendsto (fun n => ((js (φ n)).val:ℝ)/((ns (φ n):ℝ)+1)) atTop (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hratio
  have hiDegree := size_to_degree_mesh (m:=fun n => (is (φ n)).val) hnc hiSize
  have hjDegree := size_to_degree_mesh (m:=fun n => (js (φ n)).val) hnc hjSize
  have hlim := hf (ns ∘ φ) hnc (fun n => is (φ n)) (fun n => js (φ n))
    (fun n => hi (φ n)) (fun n => hj (φ n)) p.1 hp.1 p.2 hp.2 hiDegree hjDegree
  obtain ⟨n,hnorm⟩ := (hlim.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  exact (not_lt_of_ge (hbad (φ n))) hnorm

end
end jacobi.Analysis
