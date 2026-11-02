import jacobi.Finite.Eigenvectors

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The reciprocal spectral weight is exactly the complete finite squared
polynomial norm. This identity holds for the actual reconstructed
measure and supplies the normalization in the support weight limit.
Source: Christoffel function at a finite spectral atom; orthogonality
of the complete polynomial eigenvector matrix.
Use: inverse_weight_polynomial_norm identifies the support edge's weight normalization from the actual polynomial limits.
-/
namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open Matrix Finset

/-- At each actual atom, the spectral weight times the complete squared orthogonal-polynomial norm equals one.
Use: inverse_weight_polynomial_norm identifies the support edge's weight normalization from the actual polynomial limits.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: finite Christoffel function identity.
Proof: the diagonal of the actual eigenvector matrix's transpose times itself is one; its proved polynomial entries contribute the same positive spectral weight to each squared term. -/
theorem weight_polynomial_norm {N : ℕ} (M : DiscreteMeasure N) (k : Fin N) :
    M.weight k*∑i:Fin N,((M.orthogonalPolynomial i).eval (M.node k))^2=1 := by
  -- The full column norm uses every genuine polynomial coordinate, with no asymptotic normalization assumption.
  have h := congrArg (fun A:Matrix (Fin N) (Fin N) ℝ => A k k) M.reconstructedBasis.transpose_mul
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq] at h
  rw [mul_sum]
  convert h using 1
  apply sum_congr rfl
  intro i _
  rw [M.eigenvectors_polynomial]
  nlinarith [Real.sq_sqrt (M.positive k).le]

/-- The reciprocal genuine spectral weight is the complete squared polynomial norm at that same atom.
Use: Support.naturalMeasure_inverse_weight and supportMeasure_inverse_weight pass from genuine support polynomial limits to their original positive spectral weights.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: finite Christoffel function identity.
Proof: divide the actual unit column norm by the same strictly positive original spectral probability. -/
theorem inverse_weight_polynomial_norm {N : ℕ} (M : DiscreteMeasure N) (k : Fin N) :
    (M.weight k)⁻¹=∑i:Fin N,((M.orthogonalPolynomial i).eval (M.node k))^2 := by
  have h := M.weight_polynomial_norm k
  have h' := congrArg (fun x:ℝ => (M.weight k)⁻¹*x) h
  simpa only [← mul_assoc,inv_mul_cancel₀ (M.positive k).ne',one_mul,mul_one] using h'.symm

end
end jacobi.Finite.DiscreteMeasure
