import jacobi.Finite.Parity
import jacobi.Finite.Eigenvectors

/-!
Article: jacobi, Proposition C.3.
The actual canonical orthogonal polynomials inherit the exact physical
coordinate parity of the proved persymmetric eigenvectors. This
extends support polynomial limits and norming sums to the full chain.
Use: Support.naturalPolynomial_node_parity extends the support half-chain estimates to the full actual polynomial norm used in the edge weight limit.
-/
namespace jacobi.Finite
noncomputable section

/-- The actual canonical persymmetric polynomials have exact reversed-coordinate parity at every original node.
Use: Support.naturalPolynomial_node_parity extends the support half-chain estimates to the full actual polynomial norm used in the edge weight limit.
Article: jacobi, Proposition C.3.
Proof: the canonical reconstruction is genuinely persymmetric. Its actual eigenvector parity and proved polynomial entry formula have the same strictly positive square-root weight, which cancels. -/
theorem Nodes.polynomial_parity {n:ℕ} (S:Nodes (n+1)) (i k:Fin (n+1)) :
    ((S.measure S.persymmetricWeights).orthogonalPolynomial i.rev).eval (S.value k)=
      (-1:ℝ)^k.val*((S.measure S.persymmetricWeights).orthogonalPolynomial i).eval (S.value k) := by
  -- Both polynomial values are entries of the same genuine original eigenvector, with its original positive weight.
  let M := S.measure S.persymmetricWeights
  have h := eigenvector_parity S (persymmetricFiber S) M.reconstructedBasis rfl
    (persymmetricFiber_symmetric S) i k
  rw [M.eigenvectors_polynomial,M.eigenvectors_polynomial] at h
  change (M.orthogonalPolynomial i.rev).eval (M.node k)=(-1:ℝ)^k.val*(M.orthogonalPolynomial i).eval (M.node k)
  apply mul_left_cancel₀ (Real.sqrt_pos.mpr (M.positive k)).ne'
  calc
    _ = (-1:ℝ)^k.val*(Real.sqrt (M.weight k)*(M.orthogonalPolynomial i).eval (M.node k)) := h
    _ = _ := by ring

end
end jacobi.Finite
