import jacobi.Finite.LogWeights

/-!
Article: jacobi, Proposition 1.1.
Analytic dependence is proved for the actual reconstructed matrix and its
resolvent energy. The proof uses analytic Gram--Schmidt and exact spectral
reconstruction; matrix inverse analyticity is not assumed.
Source: mathlib analytic calculus and the finite spectral theorem.
Use: supplies the input family to analytic Gram--Schmidt reconstruction.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Polynomial InnerProductSpace Matrix
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (S : Nodes (n+1))

/-- Weighted monomial evaluation varies analytically with the logarithmic weights.
Use: supplies the input family to analytic Gram--Schmidt reconstruction.
Article: jacobi, Proposition 1.1.
Proof: coordinatewise positive square roots of analytic probabilities, followed
by the continuous linear equivalence from coordinate functions to Euclidean space. -/
theorem monomial_analytic (ell : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    AnalyticAt ℝ (fun v => (S.measure (logWeights S v)).evaluate (X^i.val)) ell := by
  have hc : AnalyticAt ℝ (fun v : Fin (n+1) → ℝ => fun k : Fin (n+1) =>
      Real.sqrt ((logWeights S v).val k) * (X^i.val : ℝ[X]).eval (S.value k)) ell := by
    apply AnalyticAt.pi
    intro k
    have h := (AnalyticGram.sqrt_analytic ((logWeights S ell).property.1 k)).comp
      (f := fun v => (logWeights S v).val k) (logWeights_analytic S ell k)
    exact h.mul analyticAt_const
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)).symm.analyticAt _).comp hc

/-- The canonical orthonormal polynomial vectors vary analytically.
Use: proves analyticity of every eigenvector entry and hence of J and its Green energy.
Article: jacobi, Proposition 1.1.
Proof: distinct support and positive weights give independent monomials at every
parameter; the community orthonormal basis is then normalized Gram--Schmidt. -/
theorem polynomialBasis_analytic (ell : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    AnalyticAt ℝ (fun v => (S.measure (logWeights S v)).polynomialBasis i) ell := by
  -- Independence holds at every parameter, so the chosen orthonormal basis is actual normalized Gram--Schmidt.
  have hi (v : Fin (n+1) → ℝ) : LinearIndependent ℝ
      (fun j : Fin (n+1) => (S.measure (logWeights S v)).evaluate (X^j.val)) :=
    (S.measure (logWeights S v)).evaluate_linearIndependent _ (fun _ => by simp)
      (fun _ => by simp)
  have h := AnalyticGram.normalized_analytic
    (fun v j => (S.measure (logWeights S v)).evaluate (X^j.val)) (monomial_analytic S ell) (hi ell) i
  have he (v : Fin (n+1) → ℝ) : (S.measure (logWeights S v)).polynomialBasis i =
      gramSchmidtNormed ℝ (fun j : Fin (n+1) =>
        (S.measure (logWeights S v)).evaluate (X^j.val)) i := by
    exact gramSchmidtOrthonormalBasis_apply (by simp) ((gramSchmidtNormed_linearIndependent (hi v)).ne_zero i)
  simpa only [he] using h

/-- Individual spectral matrix entries are real-analytic functions of logarithmic weights.
Use: finite sums of these entries reconstruct the matrix and its resolvent diagonal.
Article: jacobi, Proposition 1.1.
Proof: Compose the analytic basis vector with its continuous linear coordinate projection. -/
theorem eigenvectors_analytic (ell : Fin (n+1) → ℝ) (i k : Fin (n+1)) :
    AnalyticAt ℝ (fun v => (S.measure (logWeights S v)).eigenvectors i k) ell := by
  have h := polynomialBasis_analytic S ell i
  exact (((ContinuousLinearMap.proj (R := ℝ) k).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)).toContinuousLinearMap).analyticAt _).comp h

/-- Every entry of the actual logarithmically reconstructed matrix is analytic.
Use: verifies that the inverse spectral chart is real-analytic as stated in the article.
Article: jacobi, Proposition 1.1.
Proof: use the proved finite diagonalization, whose eigenvalues are constant. -/
theorem logFiber_matrix_analytic (ell : Fin (n+1) → ℝ) (i j : Fin (n+1)) :
    AnalyticAt ℝ (fun v => (logFiber S v).val.matrix i j) ell := by
  -- Use the exact spectral reconstruction with constant eigenvalues and analytic basis entries.
  have he (v : Fin (n+1) → ℝ) : (logFiber S v).val.matrix i j =
      ∑ k, (S.measure (logWeights S v)).eigenvectors i k * S.value k *
        (S.measure (logWeights S v)).eigenvectors j k := by
    rw [show (logFiber S v).val.matrix = (S.measure (logWeights S v)).multiplication from
      (S.measure (logWeights S v)).reconstructed_matrix,
      (S.measure (logWeights S v)).multiplication_diagonalization, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Nodes.measure]
  simp_rw [he]
  apply Finset.analyticAt_fun_sum
  intro k _
  exact ((eigenvectors_analytic S ell i k).mul analyticAt_const).mul (eigenvectors_analytic S ell j k)

/-- The resolvent diagonal in any orthogonal spectral basis.
Use: identifies the analytic spectral expression with the existing Jacobi Green matrix.
Article: jacobi, Proposition 1.1.
Proof: conjugate the diagonal inverse back using the already verified coordinate
resolvent theorem; then evaluate the physical diagonal entry. -/
theorem green_diagonal_spectral {N : ℕ} (J : Jacobi N) (B : SpectralBasis J.matrix)
    (h : ∀ k, 1-B.eigenvalues k ≠ 0) (i : Fin N) :
    J.green i i = ∑ k, B.Q i k^2 / (1-B.eigenvalues k) := by
  -- Conjugate the diagonal inverse back to physical coordinates before evaluating its diagonal.
  have he : J.green = B.Q * Matrix.diagonal (fun k => (1-B.eigenvalues k)⁻¹) * B.Qᵀ := by
    apply B.coordinates_injective
    rw [show B.coordinates J.green = Matrix.diagonal (fun k => (1-B.eigenvalues k)⁻¹) from
      SpectralCoordinates.coordinates_resolvent B h]
    simp only [SpectralBasis.coordinates, ← Matrix.mul_assoc, B.transpose_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, B.transpose_mul, Matrix.mul_one]
  rw [he, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The actual finite Green energy expressed in logarithmic spectral coordinates.
Use: its differential, rather than that of an auxiliary objective, is proved zero below.
Article: jacobi, Proposition 1.1.
-/
def logEnergy (ell : Fin (n+1) → ℝ) : ℝ := (logFiber S ell).val.energy

/-- The energy in logarithmic coordinates is real-analytic everywhere.
Use: evenness under reversal implies criticality at the persymmetric point.
Article: jacobi, Proposition 1.1.
Proof: its resolvent diagonal is a finite sum of squared analytic eigenvector
entries divided by fixed positive spectral gaps; energy is the sum of their squares. -/
theorem logEnergy_analytic (ell : Fin (n+1) → ℝ) : AnalyticAt ℝ (logEnergy S) ell := by
  -- Identify the original Green energy with a finite spectral expression before applying analytic calculus.
  have he (v : Fin (n+1) → ℝ) : logEnergy S v =
      ∑ i : Fin (n+1), (∑ k : Fin (n+1),
        (S.measure (logWeights S v)).eigenvectors i k^2 / (1-S.value k))^2 := by
    unfold logEnergy Jacobi.energy
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact green_diagonal_spectral _ (S.measure (logWeights S v)).reconstructedBasis
      (fun k => (sub_pos.mpr (S.interval k).2).ne') i
  change AnalyticAt ℝ (fun v => logEnergy S v) ell
  simp_rw [he]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply AnalyticAt.pow
  apply Finset.analyticAt_fun_sum
  intro k _
  exact ((eigenvectors_analytic S ell i k).pow 2).div analyticAt_const
    (sub_pos.mpr (S.interval k).2).ne'

end
end jacobi.Finite
