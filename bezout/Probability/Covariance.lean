import bezout.Probability.History
import bezout.Gains.MatrixAdmissible

/-!
Article: bezout, Equation `eq:experiment-general-mse`.
Use: actual additive oracle MSE equals the exact finite terminal bias plus the
trace of every physical response covariance, for a general covariance matrix.
Proof: square-integrable coordinates justify all finite integral interchanges;
the matrix trace identity is combined with actual martingale orthogonality.
-/

namespace bezout.Probability
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
variable {Ω J K : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- Actual second-moment matrix of a Euclidean random vector. -/
def secondMomentMatrix (X : Ω → EuclideanSpace ℝ J) (μ : Measure Ω) : Matrix J J ℝ :=
  fun j k => ∫ ω, X ω j*X ω k ∂μ

/-- Actual covariance matrix centered by the Bochner mean vector. -/
def covarianceMatrix (X : Ω → EuclideanSpace ℝ J) (μ : Measure Ω) : Matrix J J ℝ :=
  fun j k => ∫ ω, (X ω j-(∫ ω, X ω ∂μ) j)*(X ω k-(∫ ω, X ω ∂μ) k) ∂μ

omit [DecidableEq J] in
/-- Centered oracle errors have covariance equal to their actual second moment. -/
theorem covarianceMatrix_of_mean_zero (X : Ω → EuclideanSpace ℝ J)
    (hX : (∫ ω, X ω ∂μ)=0) : covarianceMatrix X μ=secondMomentMatrix X μ := by
  ext j k
  simp [covarianceMatrix, secondMomentMatrix, hX]

omit [DecidableEq J] in
/-- Every coordinate of a square-integrable Euclidean random vector is square integrable. -/
theorem coordinate_memLp {X : Ω → EuclideanSpace ℝ J} (hX : MemLp X 2 μ) (j : J) :
    MemLp (fun ω => X ω j) 2 μ :=
  hX.continuousLinearMap_comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : J => ℝ) j)

omit [DecidableEq J] in
/-- Every coordinate product needed by covariance and trace is integrable. -/
theorem coordinate_mul_integrable {X : Ω → EuclideanSpace ℝ J}
    (hX : MemLp X 2 μ) (j k : J) : Integrable (fun ω => X ω j*X ω k) μ :=
  (coordinate_memLp hX j).integrable_mul (coordinate_memLp hX k)

/-- The actual Euclidean action of an arbitrary rectangular covariance response matrix. -/
def matrixApply (A : Matrix K J ℝ) (x : EuclideanSpace ℝ J) : EuclideanSpace ℝ K :=
  Matrix.toEuclideanLin A x

omit [Fintype K] [DecidableEq K] in
/-- Physical matrix response in coordinates. -/
@[simp] theorem matrixApply_coordinate (A : Matrix K J ℝ) (x : EuclideanSpace ℝ J) (i : K) :
    matrixApply A x i=∑ j, A i j*x j := rfl

omit [DecidableEq J] [DecidableEq K] in
/-- The covariance trace expanded into its actual finite coordinate sums. -/
theorem trace_transfer (A : Matrix K J ℝ) (V : Matrix J J ℝ) :
    Matrix.trace (A*V*A.transpose)=∑ i, ∑ j, ∑ k, (A i j*A i k)*V j k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq K] in
/-- Exact coordinate square of a matrix response. -/
theorem matrixApply_norm_sq (A : Matrix K J ℝ) (x : EuclideanSpace ℝ J) :
    ‖matrixApply A x‖^2=∑ i, ∑ j, ∑ k, (A i j*A i k)*(x j*x k) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, matrixApply_coordinate]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq K] in
/-- A general covariance response contributes exactly tr(A V A^T) to actual output energy. -/
theorem integral_matrixApply_norm_sq (A : Matrix K J ℝ) {X : Ω → EuclideanSpace ℝ J}
    (hX : MemLp X 2 μ) :
    (∫ ω, ‖matrixApply A (X ω)‖^2 ∂μ)=Matrix.trace (A*secondMomentMatrix X μ*A.transpose) := by
  have hi (i : K) (j k : J) :
      Integrable (fun ω => (A i j*A i k)*(X ω j*X ω k)) μ :=
    (coordinate_mul_integrable hX j k).const_mul _
  simp_rw [matrixApply_norm_sq]
  rw [trace_transfer, integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  rfl

end
end bezout.Probability

namespace bezout.History
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
variable {N : ℕ} {Ω J : Type*} [Fintype J] [DecidableEq J]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → EuclideanSpace ℝ J}

/-- Every actual physical matrix response agrees with matrix polynomial functional calculus. -/
theorem responseOperator_matrix (h : bezout.History N) (H : Matrix J J ℝ) (s : Fin N)
    (x : EuclideanSpace ℝ J) :
    h.responseOperator (matrixEnd H) s x=bezout.Probability.matrixApply (aeval H (h.response s)) x := by
  change (aeval (matrixEnd H) (h.response s)) x=_
  rw [Polynomial.aeval_algHom_apply matrixEnd H (h.response s), matrixEnd_eq_toEuclideanLin]
  rfl

/-- The exact actual-history MSE with a general, time-dependent covariance matrix.
Use: independence is unnecessary; conditional centering suffices for the cross terms. -/
theorem integral_stochasticOutput_covariance (h : bezout.History N) (H : Matrix J J ℝ)
    (initial : EuclideanSpace ℝ J) (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) :
    (∫ ω, ‖h.stochasticOutput (matrixEnd H) initial w ω‖^2 ∂μ)=
      ‖(aeval (matrixEnd H) h.terminal) initial‖^2+
        ∑ s : Fin N, Matrix.trace
          (aeval H (h.response s)*bezout.Probability.covarianceMatrix (w s.val) μ*(aeval H (h.response s)).transpose) := by
  rw [h.integral_stochasticOutput_norm_sq _ _ hw]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [h.responseOperator_matrix]
  rw [bezout.Probability.covarianceMatrix_of_mean_zero _ (hw.integral_eq_zero s.val s.isLt)]
  exact bezout.Probability.integral_matrixApply_norm_sq _ (hw.squareIntegrable s.val s.isLt)

/-- Identically distributed centered covariance gives the article's common-V trace formula. -/
theorem integral_stochasticOutput_common_covariance (h : bezout.History N) (H : Matrix J J ℝ)
    (initial : EuclideanSpace ℝ J) (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (V : Matrix J J ℝ) (hV : ∀ s : Fin N, bezout.Probability.covarianceMatrix (w s.val) μ=V) :
    (∫ ω, ‖h.stochasticOutput (matrixEnd H) initial w ω‖^2 ∂μ)=
      ‖(aeval (matrixEnd H) h.terminal) initial‖^2+
        ∑ s : Fin N, Matrix.trace (aeval H (h.response s)*V*(aeval H (h.response s)).transpose) := by
  rw [integral_stochasticOutput_covariance h H initial hw]
  simp_rw [hV]

end
end bezout.History
