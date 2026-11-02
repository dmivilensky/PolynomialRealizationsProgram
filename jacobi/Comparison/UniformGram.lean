import jacobi.Comparison.GramTwoEdges
import jacobi.Analysis.HalfMatrixCompactness

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The complete actual two-edge Gram kernel limit is uniform over both
original physical half-chain indices. All growing spectral tails and
both middle-index conventions are included. The two kernels are the
actual continuum GL kernels, at the true matrix-size coordinates.
Use: gramKernelError_limit and gramPerturbation_uniform prove the full original uniform kernel approximation needed for finite-section coercivity and the Gram–Cholesky inverse limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Support jacobi.Reference jacobi.Analysis
open scoped Topology

/-- The actual original matrix-size-scaled Gram perturbation minus its two original continuum GL kernels, with the true alternating sign.
Use: gramKernelError_limit and gramPerturbation_uniform prove the full original uniform kernel approximation needed for finite-section coercivity and the Gram–Cholesky inverse limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def gramKernelError (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  ((n:ℝ)+1)*gramPerturbation a b ha hb n i j-
    (jacobi.GelfandLevitan.kernel a ha (matrixMesh n i) (matrixMesh n j)+
      (-1:ℝ)^(i.val+j.val)* jacobi.GelfandLevitan.kernel b hb (matrixMesh n i) (matrixMesh n j))

/-- The actual two-edge Gram approximation error vanishes along every cofinal moving physical matrix row-column pair, in the exact matrix-size coordinates.
Use: gramPerturbation_uniform applies the compact physical-square criterion and obtains the complete source uniformity in both original indices.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the complete original spectral sums already have both genuine kernel limits at the limiting physical pair. The actual degree and matrix-size coordinates have the same limits, and the original GL kernels are continuous on the closed half square. Subtracting those continuous kernel values leaves only three vanishing errors; the unchanged alternating factor has unit absolute value. -/
theorem gramKernelError_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i j:∀n:ℕ,Fin (ns n+1))
    (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1) (hj:∀ᶠn:ℕ in atTop,2*(j n).val≤ns n+1)
    {t s:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun n:ℕ => ((j n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n => gramKernelError a b ha hb (ns n) (i n) (j n)) atTop (𝓝 0) := by
  -- The same actual matrix-size coordinates remain in the genuine closed kernel domain.
  let p (n:ℕ) : ℝ × ℝ := (matrixMesh (ns n) (i n),matrixMesh (ns n) (j n))
  have hp : Tendsto p atTop (𝓝 (t,s)) :=
    (degree_to_size_mesh (m:=fun n => (i n).val) hns hit).prodMk_nhds
      (degree_to_size_mesh (m:=fun n => (j n).val) hns hjs)
  have hpmem : ∀ᶠn:ℕ in atTop,p n∈Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2) := by
    filter_upwards [hi,hj] with n hin hjn
    exact ⟨matrixMesh_mem_half hin,matrixMesh_mem_half hjn⟩
  have hpw := tendsto_nhdsWithin_iff.mpr ⟨hp,hpmem⟩
  have hFA := (jacobi.GelfandLevitan.kernel_continuousOn a ha (t,s) ⟨ht,hs⟩).tendsto.comp hpw
  have hFB := (jacobi.GelfandLevitan.kernel_continuousOn b hb (t,s) ⟨ht,hs⟩).tendsto.comp hpw
  have hbase := gramPerturbation_two_edge_limit ha hb ns hns i j hi hj ht hs hit hjs
  have hA := hFA.const_sub (jacobi.GelfandLevitan.kernel a ha t s)
  have hB := hFB.const_sub (jacobi.GelfandLevitan.kernel b hb t s)
  simp only [sub_self] at hA hB
  -- Unit absolute parity bounds the total error without choosing a parity subsequence.
  apply squeeze_zero_norm _ (by simpa only [norm_zero,zero_add] using (hbase.norm.add hA.norm).add hB.norm)
  intro n
  have he : gramKernelError a b ha hb (ns n) (i n) (j n)=
      (((ns n:ℝ)+1)*gramPerturbation a b ha hb (ns n) (i n) (j n)-
        (jacobi.GelfandLevitan.kernel a ha t s+(-1:ℝ)^((i n).val+(j n).val)* jacobi.GelfandLevitan.kernel b hb t s))+
      (jacobi.GelfandLevitan.kernel a ha t s- jacobi.GelfandLevitan.kernel a ha (p n).1 (p n).2)+
      (-1:ℝ)^((i n).val+(j n).val)*
        (jacobi.GelfandLevitan.kernel b hb t s- jacobi.GelfandLevitan.kernel b hb (p n).1 (p n).2) := by
    dsimp only [gramKernelError,p]
    ring
  rw [he]
  calc
    _ ≤ (‖((ns n:ℝ)+1)*gramPerturbation a b ha hb (ns n) (i n) (j n)-
        (jacobi.GelfandLevitan.kernel a ha t s+(-1:ℝ)^((i n).val+(j n).val)* jacobi.GelfandLevitan.kernel b hb t s)‖+
      ‖jacobi.GelfandLevitan.kernel a ha t s- jacobi.GelfandLevitan.kernel a ha (p n).1 (p n).2‖)+
      ‖(-1:ℝ)^((i n).val+(j n).val)*
        (jacobi.GelfandLevitan.kernel b hb t s- jacobi.GelfandLevitan.kernel b hb (p n).1 (p n).2)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by
      simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_one,one_pow,one_mul,Function.comp_def]

/-- The actual original two-edge Gram kernel approximation is uniform over the entire original physical matrix half square, with exact matrix-size coordinates and the genuine alternating second-edge kernel.
Use: uniform finite principal-section coercivity transfers the actual positive continuum GL forms to the original Gram matrices; the original Cholesky and eigenvector convergence then use this same uniformly controlled matrix.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: every cofinal moving original matrix pair has the proved vanishing actual kernel error, with all original spectral tails already summed. Compactness of the exact closed physical half square promotes those moving-pair limits to the full original two-index uniform limit, including both endpoint edges and the middle matrix row. -/
theorem gramPerturbation_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i j:Fin (n+1),2*i.val≤n+1→2*j.val≤n+1→
      |((n:ℝ)+1)*gramPerturbation a b ha hb n i j-
        (jacobi.GelfandLevitan.kernel a ha (matrixMesh n i) (matrixMesh n j)+
          (-1:ℝ)^(i.val+j.val)* jacobi.GelfandLevitan.kernel b hb (matrixMesh n i) (matrixMesh n j))|<ε := by
  apply half_matrix_uniform_zero (gramKernelError a b ha hb)
  intro ns hns i j hi hj t ht s hs hit hjs
  exact gramKernelError_limit ha hb ns hns i j (Eventually.of_forall hi) (Eventually.of_forall hj) ht hs hit hjs

end
end jacobi.Comparison
