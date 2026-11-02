import jacobi.Finite.DiscreteMeasure

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The triangular factorization is transported from weighted evaluation vectors to
actual polynomials. The resulting polynomials have the required degrees,
positive leading coefficients and orthonormality in the target discrete measure.
Use: its inverse transforms the original polynomials to the new orthonormal ones.
-/

namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open Polynomial Matrix
open scoped BigOperators InnerProductSpace

variable {N : ℕ} (M : DiscreteMeasure N) (p : Fin N → ℝ[X])

/-- The Cholesky factor for the input polynomial basis in the target measure.
Use: its inverse transforms the original polynomials to the new orthonormal ones.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def gramLower : Matrix (Fin N) (Fin N) ℝ :=
  Gram.lower (by simp) (fun i => M.evaluate (p i))

/-- The actual polynomial transformation by the inverse Cholesky factor.
Use: constructs the orthonormal polynomials needed for finite spectral reconstruction.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def changeOfMeasure (i : Fin N) : ℝ[X] :=
  ∑ j, (M.gramLower p)⁻¹ i j • p j

/-- Weighted evaluation of the transformed polynomials is the constructed orthonormal basis.
Use: proves all changed-measure orthogonality identities.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: evaluation is linear and the inverse-coordinate theorem reconstructs the basis. -/
theorem evaluate_changeOfMeasure (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) (i : Fin N) :
    M.evaluate (M.changeOfMeasure p i) =
      Gram.basis (by simp) (fun j => M.evaluate (p j)) i := by
  change M.evaluation (∑ j, (M.gramLower p)⁻¹ i j • p j) = _
  rw [map_sum]
  simp only [map_smul]
  exact (Gram.inverse_coordinates (by simp)
    (M.evaluate_linearIndependent p hdeg (fun j => (hlc j).ne')) i).symm

/-- Higher-degree entries of the inverse polynomial transformation vanish.
Use: proves preservation of the degree filtration.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: use inverse triangularity after proving independence by Vandermonde. -/
theorem gramLower_inverse_zero (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) {i j : Fin N} (hij : i < j) :
    (M.gramLower p)⁻¹ i j = 0 :=
  Gram.inverse_lower_triangular (by simp)
    (M.evaluate_linearIndependent p hdeg (fun k => (hlc k).ne')) hij

/-- The triangular transformation cannot increase a polynomial's indexed degree.
Use: combines with the positive top coefficient to give exact degree i.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: higher indices have zero coefficients; lower polynomials have no higher terms. -/
theorem changeOfMeasure_degree_le (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) (i : Fin N) :
    (M.changeOfMeasure p i).natDegree ≤ i.val := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [changeOfMeasure, finsetSum_coeff, coeff_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i < j
  · rw [M.gramLower_inverse_zero p hdeg hlc hij, zero_mul]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), mul_zero]

/-- The transformed top coefficient is positive and has the printed Cholesky normalization.
Use: fixes the unique positive orientation of each orthonormal polynomial.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: only the diagonal summand contributes, and the inverse diagonal is positive. -/
theorem changeOfMeasure_top (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) (i : Fin N) :
    (M.changeOfMeasure p i).coeff i.val =
      (M.gramLower p i i)⁻¹ * (p i).leadingCoeff ∧
    0 < (M.changeOfMeasure p i).coeff i.val := by
  -- Triangularity eliminates all other degree-i contributions, leaving the positive inverse diagonal.
  have hf := M.evaluate_linearIndependent p hdeg (fun j => (hlc j).ne')
  have he : (M.changeOfMeasure p i).coeff i.val =
      (M.gramLower p)⁻¹ i i * (p i).leadingCoeff := by
    simp only [changeOfMeasure, finsetSum_coeff, coeff_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [← hdeg i, coeff_natDegree]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hj | hj
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hj), mul_zero]
      · rw [M.gramLower_inverse_zero p hdeg hlc hj, zero_mul]
    · simp
  have hinv : (M.gramLower p)⁻¹ i i = (M.gramLower p i i)⁻¹ :=
    Gram.inverse_diagonal (by simp) hf i
  rw [hinv] at he
  refine ⟨he, ?_⟩
  rw [he]
  exact mul_pos (inv_pos.mpr ((Gram.lower_invertible (by simp) hf).2 i)) (hlc i)

/-- The transformed polynomials have precisely the indexed degree and positive leading term.
Use: allows another change of measure and the Jacobi three-term construction.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: combine the degree upper bound and the nonzero top coefficient. -/
theorem changeOfMeasure_degree (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) (i : Fin N) :
    (M.changeOfMeasure p i).natDegree = i.val ∧
      0 < (M.changeOfMeasure p i).leadingCoeff := by
  have ht := (M.changeOfMeasure_top p hdeg hlc i).2
  have hd := natDegree_eq_of_le_of_coeff_ne_zero
    (M.changeOfMeasure_degree_le p hdeg hlc i) ht.ne'
  exact ⟨hd, by simpa only [leadingCoeff, hd] using ht⟩

/-- The transformed polynomials are orthonormal in the new weighted measure.
Use: completes the polynomial, rather than only matrix, form of Appendix C.4.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: their weighted evaluations are exactly the Gram--Schmidt orthonormal basis. -/
theorem changeOfMeasure_orthonormal (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) :
    Orthonormal ℝ (fun i => M.evaluate (M.changeOfMeasure p i)) := by
  have he : (fun i => M.evaluate (M.changeOfMeasure p i)) =
      (Gram.basis (by simp) (fun j => M.evaluate (p j)) : Fin N → EuclideanSpace ℝ (Fin N)) :=
    funext (M.evaluate_changeOfMeasure p hdeg hlc)
  rw [he]
  exact (Gram.basis _ _).orthonormal

end
end jacobi.Finite.DiscreteMeasure
