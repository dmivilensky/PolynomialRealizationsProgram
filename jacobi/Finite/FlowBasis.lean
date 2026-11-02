import jacobi.Finite.ExponentialTilt
import jacobi.Finite.Eigenvectors

/-!
The canonical orthonormal polynomial eigenbasis along the actual weight flow.
Its entries are analytic. Polynomials of smaller degree remain orthogonal
to a fixed later basis vector after changing their evaluation weights back
to that fixed measure. Differentiating this identity determines the upper
triangle of the basis velocity without differentiating a Gram--Schmidt
algorithm or assuming an eigenvector transport equation.
Use: ResolventLax identifies the whole skew basis velocity and obtains the
matrix commutator equation for the globally constructed flow.
Article: jacobi, Proposition 5.5, Equation (5.11).
Article role: the global positive-weight construction and its exact resolvent Lax equation.
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (S : Nodes (n+1))

/-- The literal finite spectral measure used at each flow time.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def flowMeasure (w : WeightSimplex (n+1)) (t : ℝ) : DiscreteMeasure (n+1) :=
  S.measure (resolventWeights S w t)

/-- The positively oriented polynomial eigenbasis of the evolving matrix.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def flowBasis (w : WeightSimplex (n+1)) (t : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (flowMeasure S w t).eigenvectors

/-- Each genuine basis entry is analytic, so its derivative below is
the derivative of a specified concrete function.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasis_analytic (w : WeightSimplex (n+1)) (t : ℝ) (i k : Fin (n+1)) :
    AnalyticAt ℝ (fun s => flowBasis S w s i k) t :=
  (eigenvectors_analytic S _ i k).comp (resolventCoordinates_analytic S w t)

/-- The actual entrywise time derivative of the canonical eigenbasis.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def flowBasisVelocity (w : WeightSimplex (n+1)) (t : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i k => deriv (fun s => flowBasis S w s i k) t

/-- Row orthogonality holds at every real time, with the original physical
row order. It will determine the lower triangle from the upper triangle.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasis_rows (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    ∑ k,flowBasis S w t i k*flowBasis S w t j k=if i=j then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => A i j)
    (flowMeasure S w t).eigenvectors_mul_transpose
  simpa only [flowBasis,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using h

/-- Evaluate the actual row polynomial in a different fixed measure.
The square-root weight ratio is legitimate because all weights stay positive.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasis_changed_weight (w : WeightSimplex (n+1)) (s t : ℝ)
    (i k : Fin (n+1)) :
    sqrt ((resolventWeights S w t).val k)*
      (flowBasis S w s i k/sqrt ((resolventWeights S w s).val k))=
      (flowMeasure S w t).evaluate ((flowMeasure S w s).orthogonalPolynomial i) k := by
  have h := (flowMeasure S w s).eigenvectors_polynomial i k
  have hp := (sqrt_pos.mpr ((resolventWeights S w s).property.1 k)).ne'
  change flowBasis S w s i k=sqrt ((resolventWeights S w s).val k)*
    ((flowMeasure S w s).orthogonalPolynomial i).eval (S.value k) at h
  rw [h]
  simp only [DiscreteMeasure.evaluate,flowMeasure,Nodes.measure,PiLp.toLp_apply,
    mul_div_cancel_left₀ _ hp]

/-- A lower-degree row polynomial is orthogonal to a fixed later row
even when the polynomial itself comes from another flow time.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasis_mixed_orthogonal (w : WeightSimplex (n+1)) (s t : ℝ)
    (i j : Fin (n+1)) (hij : i<j) :
    ∑ k,flowBasis S w t j k*(sqrt ((resolventWeights S w t).val k)*
      (flowBasis S w s i k/sqrt ((resolventWeights S w s).val k)))=0 := by
  simp_rw [flowBasis_changed_weight]
  have hp : ((flowMeasure S w s).orthogonalPolynomial i).natDegree<j.val := by
    rw [((flowMeasure S w s).orthogonalPolynomial_degree i).1]
    exact hij
  have h := (flowMeasure S w t).polynomialBasis_orthogonal_lower hp
  simpa only [PiLp.inner_apply,Real.inner_apply,flowBasis,DiscreteMeasure.eigenvectors,mul_comm] using h

/-- The centered logarithmic velocity of the square-root probability.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def flowHalfVelocity (w : WeightSimplex (n+1)) (t : ℝ) (k : Fin (n+1)) : ℝ :=
  (resolventVelocity S k-∑ j,(resolventWeights S w t).val j*resolventVelocity S j)/2

/-- The square-root weights in the actual eigenbasis have the derivative
computed from their explicit normalized exponential formula.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowWeight_sqrt_hasDerivAt (w : WeightSimplex (n+1)) (t : ℝ) (k : Fin (n+1)) :
    HasDerivAt (fun s => sqrt ((resolventWeights S w s).val k))
      (flowHalfVelocity S w t k*sqrt ((resolventWeights S w t).val k)) t := by
  simp only [flowHalfVelocity,resolventWeights_eq_tilt]
  exact tiltWeight_sqrt_hasDerivAt w (resolventVelocity S) t k

/-- The basis velocity is skew in orthonormal row coordinates. This is
obtained by differentiating actual orthogonality at every time.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasisVelocity_skew (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    (∑ k,flowBasisVelocity S w t i k*flowBasis S w t j k)+
      (∑ k,flowBasisVelocity S w t j k*flowBasis S w t i k)=0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (flowBasis_analytic S w t i k).differentiableAt.hasDerivAt.mul
      (flowBasis_analytic S w t j k).differentiableAt.hasDerivAt)
  have he := h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
    (flowBasis_rows S w s i j).symm))
  have hz := he.unique (hasDerivAt_const t (if i=j then (1:ℝ) else 0))
  simpa only [flowBasisVelocity,Finset.sum_add_distrib,mul_comm] using hz

/-- Differentiating mixed-measure orthogonality gives the strictly upper
triangle of the basis velocity. The fixed-degree argument supplies the
triangular information that orthogonality alone would not determine.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem flowBasisVelocity_upper (w : WeightSimplex (n+1)) (t : ℝ)
    (i j : Fin (n+1)) (hij : i<j) :
    (∑ k,flowBasisVelocity S w t i k*flowBasis S w t j k)=
      (1/2:ℝ)*∑ k,resolventVelocity S k*flowBasis S w t i k*flowBasis S w t j k := by
  have hk (k : Fin (n+1)) :
      HasDerivAt (fun s => flowBasis S w t j k*(sqrt ((resolventWeights S w t).val k)*
        (flowBasis S w s i k/sqrt ((resolventWeights S w s).val k))))
        (flowBasis S w t j k*(flowBasisVelocity S w t i k-
          flowHalfVelocity S w t k*flowBasis S w t i k)) t := by
    have hp := (sqrt_pos.mpr ((resolventWeights S w t).property.1 k)).ne'
    convert (((flowBasis_analytic S w t i k).differentiableAt.hasDerivAt.div
      (flowWeight_sqrt_hasDerivAt S w t k) hp).const_mul
        (sqrt ((resolventWeights S w t).val k))).const_mul (flowBasis S w t j k) using 1
    dsimp only [flowBasisVelocity]
    field_simp [hp]
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)
  have hz : HasDerivAt (fun s => ∑ k,flowBasis S w t j k*
      (sqrt ((resolventWeights S w t).val k)*
        (flowBasis S w s i k/sqrt ((resolventWeights S w s).val k)))) 0 t := by
    convert hasDerivAt_const t (0:ℝ) using 1
    funext s
    exact flowBasis_mixed_orthogonal S w s t i j hij
  have he := h.unique hz
  have hr := flowBasis_rows S w t i j
  rw [ite_eq_right (ne_of_lt hij)] at hr
  have hn : (∑ k,flowBasis S w t j k*(flowBasisVelocity S w t i k-
        flowHalfVelocity S w t k*flowBasis S w t i k))=
      (∑ k,flowBasisVelocity S w t i k*flowBasis S w t j k)-
        (1/2:ℝ)*(∑ k,resolventVelocity S k*flowBasis S w t i k*flowBasis S w t j k)+
        ((∑ l,(resolventWeights S w t).val l*resolventVelocity S l)/2)*
          (∑ k,flowBasis S w t i k*flowBasis S w t j k) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold flowHalfVelocity
    ring
  rw [hn,hr,mul_zero,add_zero] at he
  linarith

end
end jacobi.Finite
