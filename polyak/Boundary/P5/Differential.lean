import polyak.Boundary.P5.SystemSource
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
Article: the actual Jacobian of the regularized P₅ polynomial system.
Use: partial-derivative coefficient certificates identify the genuine Frechet
derivative, rather than an unrelated matrix supplied as a hypothesis.
-/
noncomputable section
namespace polyak.Boundary.P5

/-- Article: real interpretation of a rational multivariate polynomial. -/
def polynomialValue {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (z : Fin n → ℝ) : ℝ :=
  MvPolynomial.aeval z p

/-- Article: the Frechet derivative assembled from actual formal partial derivatives. -/
def polynomialDifferential {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (z : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, polynomialValue (MvPolynomial.pderiv i p) z • ContinuousLinearMap.proj i

/-- Article: exact differentiation of every rational polynomial source. -/
theorem polynomial_hasFDerivAt {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (z : Fin n → ℝ) :
    HasFDerivAt (polynomialValue p) (polynomialDifferential p z) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C q =>
    have he : polynomialDifferential (MvPolynomial.C q : MvPolynomial (Fin n) ℚ) z=0 := by
      simp [polynomialDifferential,polynomialValue]
    rw [he]
    convert (hasFDerivAt_const (𝕜 := ℝ) (c := (q : ℝ)) (x := z)) using 1
    funext x
    simp [polynomialValue]
  | add p q hp hq =>
    have he : polynomialDifferential (p+q) z=polynomialDifferential p z+polynomialDifferential q z := by
      simp [polynomialDifferential,polynomialValue,add_smul,Finset.sum_add_distrib]
    have hf : polynomialValue (p+q)=polynomialValue p+polynomialValue q := by
      funext x
      simp [polynomialValue]
    rw [he,hf]
    exact hp.add hq
  | mul_X p j hp =>
    have he : polynomialDifferential (p*MvPolynomial.X j) z=
        polynomialValue p z • ContinuousLinearMap.proj j+z j • polynomialDifferential p z := by
      ext v
      simp [polynomialDifferential,polynomialValue,Pi.single_apply,Finset.sum_add_distrib,
        Finset.mul_sum,add_mul,apply_ite]
      ring
    have hj : HasFDerivAt (fun x : Fin n → ℝ => x j) (ContinuousLinearMap.proj j) z :=
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hf : polynomialValue (p*MvPolynomial.X j)=(fun x => polynomialValue p x*x j) := by
      funext x
      simp [polynomialValue]
    rw [he,hf]
    exact hp.mul hj

end polyak.Boundary.P5
