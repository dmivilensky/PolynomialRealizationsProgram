import jacobi.Finite.PolynomialParity
import jacobi.Support.Volterra

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The original actual support polynomials have exact physical-coordinate
parity at every genuine cosine node. In particular the positive
top-node reference solution is symmetric on the entire finite chain.
Use: topValue_rev and the complete support norming sums extend the proved half-chain limits to the genuine full original chain.
-/
namespace jacobi.Support
noncomputable section
open jacobi.Finite jacobi.Reference Real

/-- The genuine original support polynomials have exact reversed-coordinate parity at every original cosine node.
Use: topValue_rev and the complete support norming sums extend the proved half-chain limits to the genuine full original chain.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the actual support measure is the canonical persymmetric spectral measure, and its actual orthogonal polynomials have the proved exact eigenvector parity. -/
theorem naturalPolynomial_node_parity (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i k:Fin (n+1)) :
    (naturalPolynomial a b ha hb n i.rev).eval (naturalNode a b (n+1) k)=
      (-1:ℝ)^k.val*(naturalPolynomial a b ha hb n i).eval (naturalNode a b (n+1) k) := by
  rw [naturalPolynomial_eq,naturalPolynomial_eq]
  exact (naturalNodes a b ha hb (n+1)).polynomial_parity i k

/-- The actual original positive top-node reference solution is exactly symmetric under finite physical reversal.
Use: topValue_full_uniform and the genuine top-node spectral weight limit use the full original polynomial norm rather than a separately assumed reflected reference family.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual first spectral index has positive parity; its original cosine node is exactly the original top-node energy. -/
theorem topValue_rev (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) :
    topValue a b ha hb n i.rev=topValue a b ha hb n i := by
  have h := naturalPolynomial_node_parity a b ha hb n i 0
  simpa [topValue,naturalNode,modelAngle_step] using h

end
end jacobi.Support
