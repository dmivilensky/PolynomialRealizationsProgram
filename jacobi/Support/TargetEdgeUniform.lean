import jacobi.Support.MovingEdge
import jacobi.Analysis.CellGeometry
import jacobi.GelfandLevitan.QuadraticSeries

/-!
Article: jacobi, Proposition C.3.
The actual support polynomials at a fixed original target zero have
their full uniform reference-wave limit in the true matrix-size spatial
coordinates. The normalization remains the original degree power used
in the exact target/support Schur transformation.
Use: the target eigenvector proof replaces every preceding support polynomial in its genuine growing Schur row by the same reference wave.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology

/-- The actual fixed-target support edge limit is uniform on the whole
physical half chain in the original matrix-size coordinates.
Use: the target eigenvector proof replaces every preceding support
polynomial in its genuine growing Schur row by the same reference wave.
Article: jacobi, Proposition C.3.
Proof: every cofinal moving physical index has the proved genuine
reference-wave limit. The degree and matrix-size coordinates have the
same limit; compactness of the closed physical half interval makes
the resulting actual error uniform, including the original midpoint. -/
theorem supportPolynomial_target_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    ∀ ε:ℝ,0<ε → ∃N:ℕ,∀n≥N,∀i:Fin (n+1),2*i.val≤n+1 →
      |(n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb n i).eval
          (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))-
        (topConstant a b*π^gamma a)*realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i)|<ε := by
  -- Uniformity is obtained for the actual polynomials, without an auxiliary edge certificate.
  let err (n:ℕ) (i _:Fin (n+1)) : ℝ :=
    (n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb n i).eval
      (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))-
      (topConstant a b*π^gamma a)*realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i)
  have hu := half_matrix_uniform_zero err (by
    intro ns hns i _ hi _ t ht _ _ hit _
    have hP := supportPolynomial_target_limit ha hb k ns hns i (Eventually.of_forall hi) ht hit
    have hF := ((realSolution_continuousAt ha (jacobi.Bessel.sigma a ha k) ht).tendsto.comp
      (degree_to_size_mesh (m:=fun r => (i r).val) hns hit)).const_mul (topConstant a b*π^gamma a)
    simpa only [err,matrixMesh,Function.comp_def,sub_self] using hP.sub hF)
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  refine ⟨N,fun n hn i hi => ?_⟩
  simpa only [Real.norm_eq_abs] using hN n hn i 0 hi (by simp)

/-- The actual degree-normalized support values at a fixed original
target edge have one uniform bound on all physical half-chain indices.
Use: uniform coefficient and support-wave errors remain small after
summing the complete growing target-polynomial Schur row.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: the proved actual uniform edge error is eventually below one.
The genuine reference wave is continuous on the compact physical half
interval and its actual shared-unit-interval extension has a fixed norm. -/
theorem supportPolynomial_target_scaled_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    ∃ B:ℝ,0<B ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),2*i.val≤n+1 →
      |(n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb n i).eval
        (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))|≤B := by
  -- The compact reference bound concerns the same original matrix-size sample.
  let A := topConstant a b*π^gamma a
  let W := realHalfWave a ha (jacobi.Bessel.sigma a ha k)
  obtain ⟨N,hN⟩ := supportPolynomial_target_uniform ha hb k 1 (by norm_num)
  refine ⟨1+|A| * ‖W‖,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  intro i hi
  have hf : |realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i)|≤‖W‖ := by
    have hh := W.norm_coe_le_norm (matrixPoint n i)
    change ‖realSolution a (jacobi.Bessel.sigma a ha k) (min (matrixMesh n i) (1/2))‖≤‖W‖ at hh
    simpa only [min_eq_left (matrixMesh_mem_half hi).2,Real.norm_eq_abs] using hh
  have he := hN n hn i hi
  have hh := abs_add_le
    ((n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb n i).eval
      (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))-
      A*realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i))
    (A*realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i))
  rw [sub_add_cancel] at hh
  have hAF : |A*realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i)|≤|A| * ‖W‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg A)
  exact hh.trans (add_le_add he.le hAF)

end
end jacobi.Support
