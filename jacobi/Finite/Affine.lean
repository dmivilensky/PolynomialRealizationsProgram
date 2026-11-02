import jacobi.Finite.Basic

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Positive affine transformation of arbitrary finite Jacobi data preserves
the actual symmetric matrix, irreducibility and original zero-tail
convention. The support application uses the literal c_n,d_n correction.
Use: Support.supportChain is the original corrected support matrix c_n*J_n^natural+d_n*I.
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix chebyshev1 chebyshev2

/-- The actual affine transformation of an arbitrary finite Jacobi chain, with its original zero tails fixed.
Use: Support.supportChain is the original corrected support matrix c_n*J_n^natural+d_n*I.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def affine {n : ℕ} (J : Jacobi n) (c d : ℝ) : Jacobi n where
  data := {
    b := fun m => if m<n then c*J.data.b m+d else 0
    aSq := fun m => c^2*J.data.aSq m }
  coupling_nonneg m := mul_nonneg (sq_nonneg c) (J.coupling_nonneg m)
  coupling_zero := by change c^2*J.data.aSq 0=0; rw [J.coupling_zero,mul_zero]
  diagonal_tail m hm := by simp [not_lt.mpr hm]
  coupling_tail m hm := by change c^2*J.data.aSq m=0; rw [J.coupling_tail m hm,mul_zero]

/-- The genuine affine Jacobi encoding is exactly the actual matrix affine transformation whenever the original scale is nonnegative.
Use: the support chain has exactly the original affine-image spectrum and unchanged spectral weights and polynomials.
Article: jacobi, Theorem C.5.
Proof: diagonal and zero-band entries retain the literal original affine formulas. For each actual adjacent entry, nonnegative scale and genuine squared-coupling nonnegativity identify sqrt(c^2*a^2)=c*sqrt(a^2). -/
theorem affine_matrix {n : ℕ} (J : Jacobi n) {c : ℝ} (hc : 0≤c) (d : ℝ) :
    (affine J c d).matrix=c • J.matrix+Matrix.scalar (Fin n) d := by
  -- The square-root sign is justified by the actual nonnegative scale; no matrix square root is substituted.
  have hs (m : ℕ) : Real.sqrt (c^2*J.data.aSq m)=c*Real.sqrt (J.data.aSq m) := by
    rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Jacobi.matrix,JacobiData.matrix_apply,Nat.zero_add,affine,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.scalar_apply,Matrix.diagonal_apply]
  split_ifs <;> simp_all only [mul_zero,add_zero]

/-- A nonzero affine scale preserves genuine original finite irreducibility.
Use: the actual corrected support chain remains an admissible positive-coupling original chain throughout its parameter range.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: every original positive squared coupling is multiplied by the genuine strictly positive squared nonzero scale. -/
theorem affine_irreducible {n : ℕ} {J : Jacobi n} (hJ : J.Irreducible) {c : ℝ} (hc : c≠0) (d : ℝ) :
    (affine J c d).Irreducible := by
  intro m hm hmn
  exact mul_pos (sq_pos_of_ne_zero hc) (hJ m hm hmn)

end
end jacobi.Finite
