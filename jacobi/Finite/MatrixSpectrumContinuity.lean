import chebyshev2.Continuum.MatrixTraceBound
import chebyshev2.Continuum.SpectralPerturbation

/-!
Finite positive-matrix spectrum continuity in the full l1 distance.
The previously proved trace-norm perturbation theorem bounds the sorted,
zero-padded spectra by the entrywise l1 matrix distance. This works with
repeated eigenvalues and makes continuity of a chosen ordered eigenbasis
unnecessary.
Use: ClosedTransfer controls the spectral error when shrinking reducible
matrices whose spectrum contains minus one.
Article: jacobi, Lemma 5.2.
Article role: continuity and contractive approximation in the closed-fibre transfer proof.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Real Filter chebyshev2.Continuum
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/-- Entrywise l1 distance between finite real matrices.
Article: jacobi, Lemma 5.2.
-/
def matrixEntryDistance (A B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i,∑ j,|A i j-B i j|

/-- A positive matrix gives a positive operator on the actual Euclidean
space used by the existing spectral stability theorem.
Article: jacobi, Lemma 5.2.
-/
theorem matrix_operator_positive {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).IsPositive := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hA

/-- The full sorted spectral l1 error is bounded by the finite entrywise
matrix error. No simplicity, gap or eigenvector-continuity assumption appears.
Article: jacobi, Lemma 5.2.
-/
theorem matrixSpectrum_distance_le (A B : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∑' j,|(matrixSpectralData A hA).eigenvalue j-
      (matrixSpectralData B hB).eigenvalue j|)≤matrixEntryDistance A B := by
  have hD : TraceBound
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A-Matrix.toEuclideanCLM (𝕜 := ℝ) B)
      (matrixEntryDistance A B) := by
    simpa only [map_sub,Matrix.sub_apply,matrixEntryDistance] using matrix_traceBound (A-B)
  exact eigenvalue_l1_le_traceBound
    (isCompactOperator_of_locallyCompactSpace_dom _) (isCompactOperator_of_locallyCompactSpace_dom _)
    (matrix_operator_positive hA) (matrix_operator_positive hB)
    (matrixSpectralData A hA) (matrixSpectralData B hB) hD

/-- Ordinary matrix convergence makes the finite entrywise error tend
to zero. Positivity is not needed for this topological step.
Article: jacobi, Lemma 5.2.
-/
theorem matrixEntryDistance_limit {ι : Type*} {l : Filter ι}
    {A : ι → Matrix (Fin N) (Fin N) ℝ} {B : Matrix (Fin N) (Fin N) ℝ}
    (h : Tendsto A l (𝓝 B)) :
    Tendsto (fun x => matrixEntryDistance (A x) B) l (𝓝 0) := by
  have hij (i j : Fin N) : Tendsto (fun x => |A x i j-B i j|) l (𝓝 0) := by
    have h0 := ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i)) j).sub (tendsto_const_nhds (x := B i j))
    simpa only [sub_self,abs_zero] using h0.abs
  simpa only [matrixEntryDistance,Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hij i j))

/-- The padded sorted spectrum has exactly the finite matrix trace,
including eigenvalue multiplicities.
Article: jacobi, Lemma 5.2.
-/
theorem matrixSpectrum_tsum_trace (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) :
    (∑' j,(matrixSpectralData A hA).eigenvalue j)=trace A := by
  rw [(matrixSpectralData A hA).eigenvalue_tsum]
  change (∑' i,hA.isHermitian.eigenvalues i)=trace A
  rw [tsum_fintype]
  simpa only [RCLike.ofReal_real_eq_id,id_eq] using hA.isHermitian.trace_eq_sum_eigenvalues.symm

end
end jacobi.Finite
