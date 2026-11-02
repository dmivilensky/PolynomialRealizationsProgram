import jacobi.Finite.Affine
import jacobi.Finite.NormalizedPolynomials

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual normalized recurrence polynomials obey the original positive
affine change of spectral variable. Both the continuant and its coupling
normalization are transformed explicitly, so the result concerns the
same genuine orthogonal polynomials used in the finite Gram matrix.
Use: normalizedLeading_affine cancels this precise factor against the transformed leading continuant.
-/
namespace jacobi.Finite
noncomputable section
open Real Polynomial chebyshev1 chebyshev2

/-- Positive affine scaling multiplies the actual coupling product by the corresponding power of the scale.
Use: normalizedLeading_affine cancels this precise factor against the transformed leading continuant.
Article: jacobi, Proposition 6.1.
Proof: each actual square root becomes c times its original square root, and the product contains exactly m factors. -/
theorem linkProduct_affine {n : ℕ} (J : Jacobi n) {c : ℝ} (hc : 0≤c) (d : ℝ) (m : ℕ) :
    (affine J c d).data.linkProduct m=c^m*J.data.linkProduct m := by
  simp only [JacobiData.linkProduct,affine,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]

/-- The actual leading continuant has the exact affine evaluation formula through the full original finite characteristic degree.
Use: normalizedLeading_affine identifies the original corrected support polynomials with the original natural family after its printed change of spectral variable.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: two-step induction in the original three-term recurrence gives the two initial values and transforms each genuine diagonal and squared coupling with its exact affine power. -/
theorem leading_affine_eval {n : ℕ} (J : Jacobi n) {c : ℝ} (hc : c≠0) (d x : ℝ)
    (m : ℕ) (hm:m≤n) :
    ((affine J c d).data.leading m).eval x=
      c^m*(J.data.leading m).eval ((x-d)/c) := by
  -- The bound on the degree ensures every diagonal used is an actual matrix row, before the original zero tail.
  induction m using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading,JacobiData.block]
  | one =>
    have hrow : 0<n := by omega
    simp only [JacobiData.leading,JacobiData.block,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,affine,ite_eq_left_iff.mpr (fun h => False.elim (h hrow)),pow_one]
    field_simp
    ring
  | more m h0 h1 =>
    have hrow : m+1<n := by omega
    have hrec (K : Jacobi n) : K.data.leading (m+2)=
        (X-C (K.data.b (m+1)))*K.data.leading (m+1)-C (K.data.aSq (m+1))*K.data.leading m := by
      simp only [JacobiData.leading,JacobiData.block,Nat.zero_add]
    rw [hrec,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_C,h0 (by omega),h1 (by omega),hrec]
    simp only [affine,ite_eq_left_iff.mpr (fun h => False.elim (h hrow)),Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_C,pow_succ]
    field_simp
    ring

/-- The genuine normalized recurrence polynomial transforms by the original positive affine spectral substitution.
Use: Support.supportPolynomial_affine connects the actual corrected orthogonal family to the natural family for the support edge limit and envelopes.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: polynomial evaluation reduces the identity to the genuine affine continuant formula and coupling-product formula. The positive scale makes its exact power nonzero, so these same normalization factors cancel. -/
theorem normalizedLeading_affine {n : ℕ} (J : Jacobi n) {c : ℝ} (hc : 0<c) (d : ℝ)
    (m : ℕ) (hm:m≤n) :
    normalizedLeading (affine J c d) m=
      (normalizedLeading J m).comp (C c⁻¹*(X-C d)) := by
  -- Equality is proved for the actual polynomials, not just at the finitely many support nodes.
  apply Polynomial.funext
  intro x
  simp only [normalizedLeading,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,
    Polynomial.eval_sub,Polynomial.eval_X,linkProduct_affine J hc.le d m,
    leading_affine_eval J hc.ne' d x m hm,mul_inv_rev]
  rw [show c⁻¹*(x-d)=(x-d)/c by ring]
  field_simp

end
end jacobi.Finite
