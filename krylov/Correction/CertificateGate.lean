import krylov.Correction.CertificatePhase
import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, prop:deep, independent actual source expressions.
Use: Exact original gate acceptance from checked rational pairing inequalities.
Source: the original seven rational rows and positive diagonal root,
exact existing physical congruence and real RFC array semantics.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine normalized observed-defect squared Frobenius norm is its exact rational pairing sum on the true positive-energy domain.
Use: Certify actual gate acceptance without introducing a square-root expression or a norm assumption.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Expand the real observed entries and square their genuine positive square-root denominators. -/
theorem pairDefect_hsSq {p : ℕ} (s y : Fin p → E)
    (he : ∀ i, 0 < inner ℝ (s i) (y i)) :
    chebyshev1.hsSq (pairDefect s y)=
      ∑ i, ∑ j, (inner ℝ (s i) (y j)-inner ℝ (s j) (y i))^2/
        (inner ℝ (s i) (y i)*inner ℝ (s j) (y j)) := by
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change (_/Real.sqrt (_*_))^2=_
  rw [div_pow,Real.sq_sqrt (mul_nonneg (he i).le (he j).le)]

/-- A genuine strict rational squared-defect bound implies actual spectral RFC gate acceptance.
Use: Turn independently checked arithmetic into the real original observed-data gate.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: The exact true squared Hilbert–Schmidt identity and reused actual spectral comparison give a strict unit spectral bound. -/
theorem pairDefect_gate_of_squared_bound {p : ℕ} (s y : Fin p → E)
    (he : ∀ i, 0 < inner ℝ (s i) (y i))
    (hsmall : (∑ i, ∑ j, (inner ℝ (s i) (y j)-inner ℝ (s j) (y i))^2/
      (inner ℝ (s i) (y i)*inner ℝ (s j) (y j)))<1) : ‖pairDefect s y‖<1 := by
  have hsq := pairDefect_hsSq s y he
  have hh := chebyshev1.hsNorm_sq (pairDefect s y)
  have hp : chebyshev1.hsNorm (pairDefect s y)<1 := by
    nlinarith [chebyshev1.hsNorm_nonneg (pairDefect s y)]
  exact (spectral_le_hsNorm _).trans_lt hp

/-- The actual rational expression for the normalized observed-defect squared Frobenius sum.
Use: Compile genuine gate conditions in the unchanged integer arithmetic checker.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def termDefectSquare {n p : ℕ} (s y : Fin p → Fin n → Term) : Term :=
  termSum (fun i => termSum (fun j =>
    .mul (.mul (.add (termDot (s i) (y j)) (.neg (termDot (s j) (y i))))
        (.add (termDot (s i) (y j)) (.neg (termDot (s j) (y i)))))
      (.inv (.mul (termDot (s i) (y i)) (termDot (s j) (y j))))))

/-- The compiled squared-defect expression has exactly the true rational observed-pairing semantics.
Use: Keep the numerical gate test tied to the original physical stored arrays.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Apply the proved actual finite-sum and Euclidean pairing semantics, with the original squared numerator and energy-product denominator. -/
theorem termDefectSquare_value {n p : ℕ} (s y : Fin p → Fin n → Term) (x : ℕ → ℝ) :
    (termDefectSquare s y).value x=
      ∑ i, ∑ j, (inner ℝ (euclideanValue (s i) x) (euclideanValue (y j) x)-
        inner ℝ (euclideanValue (s j) x) (euclideanValue (y i) x))^2/
        (inner ℝ (euclideanValue (s i) x) (euclideanValue (y i) x)*
          inner ℝ (euclideanValue (s j) x) (euclideanValue (y j) x)) := by
  simp only [termDefectSquare,termSum_value,Expr.value,termDot_inner,sub_eq_add_neg,pow_two,div_eq_mul_inv]

end
end krylov.Correction.Certificate
