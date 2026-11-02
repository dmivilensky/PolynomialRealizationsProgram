import jacobi.Comparison.UniformEigenvectorLimit
import jacobi.Analysis.FloorMatrixIndex
import jacobi.GelfandLevitan.FullWaveProfiles

/-!
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
The genuine finite eigenvectors converge to the original signed full
waves at the exact printed floor rows. Their squared moving-row limits
are precisely the original spectral profiles on the whole interval.
Use: this is all of Theorem 2.1, and supplies the actual physical step representatives for trace-norm convergence in Theorem 2.1.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology

/-- The actual signed eigenvector converges at the article's exact
physical floor row to the same full continuum eigenfunction.
Use: this is all of Theorem 2.1, and supplies the actual physical
step representatives for trace-norm convergence in Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: apply the proved full moving-row limit to the genuine finite
floor index and its already proved matrix-size mesh convergence. -/
theorem target_eigenvector_floor_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n:ℕ => sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n
      (floorMatrixIndex n t ht) k) atTop
      (𝓝 (fullWaveMap a ha k ⟨t,⟨ht.1.le,ht.2.le⟩⟩)) :=
  target_eigenvector_full_limit ha hb k id tendsto_id (fun n => floorMatrixIndex n t ht)
    (floorMatrixMesh_tendsto t ht)

/-- The true full physical moving-row squares converge to the original
spectral profile, including both endpoints and the physical midpoint.
Use: spectral summation proves the actual diagonal profile of Theorem 2.1;
products of the signed limits prove the full Green-matrix limit in Theorem 2.1.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: square the genuine signed full moving-row limit and insert the
proved original identity upsilon_k squared equals Phi_k. The positive
square root of the actual matrix dimension cancels exactly. -/
theorem target_eigenvector_sq_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    {t:Interval} (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/((ns r:ℝ)+1)) atTop (𝓝 (t:ℝ))) :
    Tendsto (fun r => ((ns r:ℝ)+1)*(targetEigenvectorEntry a b ha hb (ns r) (i r) k)^2)
      atTop (𝓝 (spectralProfile a ha k t)) := by
  simpa only [mul_pow,sq_sqrt (by positivity : (0:ℝ)≤(ns _ :ℝ)+1),fullWaveMap_sq] using
    (target_eigenvector_full_limit ha hb k ns hns i hit).pow 2

end
end jacobi.Comparison
