import jacobi.Finite.AffinePolynomials
import jacobi.Finite.Reversal

/-!
Article: jacobi, Theorem C.5.
Spectral reflection negates the genuine finite Jacobi diagonal while
retaining its positive adjacent entries. Its exact characteristic
reflection and its commutation with physical reversal are proved here;
the support application then uses the earlier uniqueness theorem.
Use: Support.naturalChain_swap identifies it with the actual support chain having the exchanged original endpoint parameters.
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix Polynomial chebyshev1 chebyshev2

/-- The genuine positive-coupling spectral reflection of a finite Jacobi chain.
Use: Support.naturalChain_swap identifies it with the actual support chain having the exchanged original endpoint parameters.
Article: jacobi, Proposition 6.1.
-/
def reflect {n : ℕ} (J : Jacobi n) : Jacobi n := affine J (-1) 0

/-- Spectral reflection has the exact reflected characteristic polynomial at every real point.
Use: the actual reflected support chain is put in the original swapped cosine-node fibre before applying genuine persymmetric uniqueness.
Article: jacobi, Theorem C.5.
Proof: both actual leading continuants are their genuine whole characteristic polynomials; the already proved affine continuant identity at scale minus one gives the exact sign and change of spectral variable. -/
theorem reflect_charpoly_eval {n : ℕ} (J : Jacobi n) (x : ℝ) :
    (reflect J).matrix.charpoly.eval x=(-1:ℝ)^n*J.matrix.charpoly.eval (-x) := by
  have h := leading_affine_eval J (by norm_num : (-1:ℝ)≠0) 0 x n le_rfl
  change ((reflect J).data.leading n).eval x=(-1:ℝ)^n*(J.data.leading n).eval ((x-0)/(-1)) at h
  simp only [JacobiData.leading,J.data.block_eq_charpoly J.coupling_nonneg,
    (reflect J).data.block_eq_charpoly (reflect J).coupling_nonneg,sub_zero,div_neg,div_one] at h
  exact h

/-- Physical reversal commutes with every actual finite affine Jacobi transformation, including spectral reflection.
Use: reflect_persymmetric proves genuine physical persymmetry of the reflected support matrix without introducing extra spectral or matrix hypotheses.
Article: jacobi, Theorem C.5.
Proof: compare the genuine diagonal and squared-coupling functions. All actual used rows have the same affine values, and every remaining original finite tail is zero. -/
theorem reverse_affine {n : ℕ} (J : Jacobi n) (c d : ℝ) :
    reverse (affine J c d)=affine (reverse J) c d := by
  -- The original finite zero-tail convention is retained on both sides.
  apply Jacobi.ext
  apply congrArg₂ JacobiData.mk
  · funext m
    by_cases hm:m<n
    · simp only [reverse,affine,ite_eq_left hm,ite_eq_left (by omega : n-1-m<n)]
    · simp only [reverse,affine,ite_eq_right hm]
  · funext m
    by_cases hm:0<m ∧ m<n
    · simp only [reverse,affine,ite_eq_left hm]
    · simp only [reverse,affine,ite_eq_right hm,mul_zero]

/-- The actual spectral reflection of a genuinely reversal-fixed chain remains physically persymmetric.
Use: the support parameter swap follows from actual persymmetric fibre uniqueness, with this premise fully discharged.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the genuine reverse commutes with the actual reflection and the original chain is fixed by that reverse. -/
theorem reflect_persymmetric {n : ℕ} {J : Jacobi n} (hJ:reverse J=J) :
    (reflect J).matrix.submatrix Fin.rev Fin.rev=(reflect J).matrix := by
  rw [← reverse_matrix]
  exact congrArg Jacobi.matrix (show reverse (reflect J)=reflect J by rw [reflect,reverse_affine,hJ])

end
end jacobi.Finite
