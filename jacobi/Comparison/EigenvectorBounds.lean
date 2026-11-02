import jacobi.Comparison.TargetWeightedBounds
import jacobi.Finite.PolynomialParity

/-!
Article: jacobi, Proposition C.3.
The actual target eigenvectors have their exact physical parity and
one uniform matrix-size bound over the complete physical chain and
the entire original spectrum. No limiting eigenvector premise is used.
Use: the full eigenvector bound and the signed limiting eigenfunctions extend the original half-chain estimates across the physical midpoint.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter jacobi.Finite
open scoped Topology

/-- The actual canonical target eigenvectors have exactly the original
ordered spectral parity under physical-coordinate reversal.
Use: the full eigenvector bound and the signed limiting eigenfunctions
extend the original half-chain estimates across the physical midpoint.
Article: jacobi, Theorem 2.1.
Proof: the genuine target measure is the already proved canonical
persymmetric measure at the actual Jacobi zeros. Its polynomial parity
and exact positive square-root weight formula give this same true sign. -/
theorem target_eigenvector_parity (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i k:Fin (n+1)) :
    (targetMeasure a b ha hb n).reconstructedBasis.Q i.rev k=
      (-1:ℝ)^k.val*(targetMeasure a b ha hb n).reconstructedBasis.Q i k := by
  have hp : (targetPolynomial a b ha hb n i.rev).eval ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k)=
      (-1:ℝ)^k.val*(targetPolynomial a b ha hb n i).eval ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k) :=
    (jacobi.Jacobi.nodes a b ha hb (n+1)).polynomial_parity i k
  rw [target_eigenvector_polynomial,target_eigenvector_polynomial,hp]
  ring

/-- The genuine original target eigenvectors obey one uniform scaled
absolute bound over all physical and spectral indices simultaneously.
Use: spectral tails and dominated convergence in Theorems A and D use
this complete growing-array bound for the actual original matrices.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: on the physical half, the exact polynomial eigenvector formula
turns the established genuine target-weighted bound into the displayed
one with the true matrix size N. Actual persymmetric parity preserves
absolute values and transfers it to every other physical coordinate. -/
theorem target_eigenvector_uniform_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ n:ℕ in atTop, ∀ i k:Fin (n+1),
      sqrt ((n:ℝ)+1)*|(targetMeasure a b ha hb n).reconstructedBasis.Q i k|≤C := by
  -- First bound the genuine polynomial formula on the half chain, then use exact physical parity.
  obtain ⟨C,hC,hbound⟩ := targetPolynomial_weighted_bound ha hb
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with n hn
  have hhalf (i k:Fin (n+1)) (hi:2*i.val≤n+1) :
      sqrt ((n:ℝ)+1)*|(targetMeasure a b ha hb n).reconstructedBasis.Q i k|≤C := by
    rw [target_eigenvector_polynomial,abs_mul,abs_of_pos (sqrt_pos.mpr ((targetMeasure a b ha hb n).positive k))]
    rw [← mul_assoc,← Real.sqrt_mul (by positivity : (0:ℝ)≤(n:ℝ)+1)]
    exact hn i hi k
  intro i k
  by_cases hi : 2*i.val≤n+1
  · exact hhalf i k hi
  · have hr : 2*i.rev.val≤n+1 := by simp only [Fin.val_rev]; omega
    have hh := hhalf i.rev k hr
    rw [target_eigenvector_parity,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] at hh
    exact hh

/-- The complete actual original finite eigenvector array has the
uniform squared source bound N*phi_(N,k)(i)^2<=C.
Use: the finite resolvent tail estimates for Theorem 2.1, Theorem 2.1
and Theorem C.5 use this genuine bound at every growing spectral index.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: square the proved true nonnegative absolute bound, use the exact
positive square-root identity for the original matrix size, and retain
the same original physical and spectral index ranges. -/
theorem target_eigenvector_uniform_sq_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ n:ℕ in atTop, ∀ i k:Fin (n+1),
      ((n:ℝ)+1)*((targetMeasure a b ha hb n).reconstructedBasis.Q i k)^2≤C := by
  obtain ⟨C,hC,hbound⟩ := target_eigenvector_uniform_bound ha hb
  refine ⟨C^2,by positivity,?_⟩
  filter_upwards [hbound] with n hn
  intro i k
  have hh := (sq_le_sq₀ (by positivity : (0:ℝ)≤sqrt ((n:ℝ)+1)*
    |(targetMeasure a b ha hb n).reconstructedBasis.Q i k|) hC.le).mpr (hn i k)
  simpa only [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤(n:ℝ)+1),sq_abs] using hh

end
end jacobi.Comparison
