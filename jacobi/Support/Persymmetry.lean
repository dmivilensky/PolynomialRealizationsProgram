import jacobi.Support.Chain
import jacobi.Support.CoefficientReflection
import jacobi.Finite.Reversal

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The actual original support matrix is persymmetric in every finite
dimension. The proof checks its original diagonal and squared-coupling
reversal identities and then reuses the earlier finite reversal theorem.
Use: naturalChain_reverse identifies the entire original matrix with its physical reversal.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference chebyshev2

/-- The actual original support diagonal has its exact original finite reversal symmetry.
Use: naturalChain_reverse identifies the entire original matrix with its physical reversal.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the original A and C coefficients exchange under the proved exact index reflection, leaving their original sum unchanged. -/
theorem diagonal_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    diagonal a b n (n-1-m)=diagonal a b n m := by
  rw [diagonal,diagonal,coefficientA_reflection ha hb hm,coefficientC_reflection ha hb hm]
  ring

/-- Every actual original support squared coupling is unchanged under physical edge reversal, including both zero boundary couplings.
Use: naturalChain_reverse proves the literal original finite Jacobi data reversal equality.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: handle the actual two zero endpoints separately. On an original interior edge the independently proved A/C reflections interchange the genuine two positive factors. -/
theorem naturalChain_coupling_reflection (a b : ℝ) (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m≤n) :
    (naturalChain a b ha hb n).data.aSq (n-m)=(naturalChain a b ha hb n).data.aSq m := by
  -- The finite boundary couplings are the genuine fixed zeros of the reused Jacobi type.
  by_cases hm0 : m=0
  · subst m
    rw [Nat.sub_zero,(naturalChain a b ha hb n).coupling_tail n le_rfl,
      (naturalChain a b ha hb n).coupling_zero]
  by_cases hmn : m=n
  · subst m
    rw [Nat.sub_self,(naturalChain a b ha hb n).coupling_zero,
      (naturalChain a b ha hb n).coupling_tail n le_rfl]
  rw [naturalChain_coupling a b ha hb (by omega : 0<n-m) (by omega : n-m<n),
    naturalChain_coupling a b ha hb (by omega : 0<m) (by omega : m<n)]
  have hA := coefficientA_reflection ha hb (show m<n by omega)
  have hC := coefficientC_reflection ha hb (show m-1<n by omega)
  rw [show n-m-1=n-1-m by omega,hA,
    show n-m=n-1-(m-1) by omega,hC]
  ring

/-- The actual finite Jacobi support data equal their genuine original physical reversal.
Use: naturalChain_persymmetric applies the already proved finite matrix-reversal bridge, preserving the same actual matrix and coefficients.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: compare the original finite diagonal and coupling functions. Their proved actual reversal identities handle every used index; the original fixed tails handle the remaining coordinates. -/
theorem naturalChain_reverse (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    jacobi.Finite.reverse (naturalChain a b ha hb n)=naturalChain a b ha hb n := by
  -- Reuse the earlier coefficient-level reversal construction; no new matrix convention is introduced.
  apply Jacobi.ext
  apply congrArg₂ chebyshev1.JacobiData.mk
  · funext m
    by_cases hm : m<n
    · simp only [naturalChain,ite_eq_left hm,ite_eq_left (by omega : n-1-m<n)]
      exact diagonal_reflection ha hb hm
    · simp only [ite_eq_right hm]
  · funext m
    by_cases hm : 0<m ∧ m<n
    · rw [ite_eq_left hm,naturalChain_coupling_reflection a b ha hb hm.2.le]
      rfl
    · rw [ite_eq_right hm]
      rw [ite_eq_right hm]

/-- The actual original support matrix is genuinely persymmetric at every finite dimension and throughout the full original parameter range.
Use: its original spectral weights are the canonical reciprocal-characteristic-derivative weights, which drive the finite-to-continuum Gram comparison.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the independently proved actual original coefficient reversal equals the genuine finite reversal, whose matrix is the original simultaneous row and column reversal. -/
theorem naturalChain_persymmetric (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (naturalChain a b ha hb n).matrix.submatrix Fin.rev Fin.rev=(naturalChain a b ha hb n).matrix := by
  rw [← jacobi.Finite.reverse_matrix,naturalChain_reverse]

end
end jacobi.Support
