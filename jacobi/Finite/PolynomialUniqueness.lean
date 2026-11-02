import jacobi.Finite.OrthogonalPolynomials

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Positive leading coefficients and orthonormality determine the polynomial family
uniquely. Thus the change of measure constructs the same canonical polynomials
regardless of the original degree-graded basis, as required for comparison chains.
Source: uniqueness of normalized orthogonal polynomials for a positive measure.
Use: identifies the Appendix C.4 and Schur constructions with the target polynomials.
-/
namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open Polynomial InnerProductSpace
open scoped BigOperators InnerProductSpace

variable {N : ℕ} (M : DiscreteMeasure N)

/-- A degree-graded positively normalized orthonormal family is the canonical family.
Use: identifies the Appendix C.4 and Schur constructions with the target polynomials.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: induction on degree. Expansion in the canonical basis has only the current
coefficient: later coefficients vanish by degree, earlier ones by orthonormality
and induction. Positivity of the leading term fixes the unit scalar to one. -/
theorem orthogonalPolynomial_unique (p : Fin N → ℝ[X])
    (hdeg : ∀ i, (p i).natDegree = i.val) (hlc : ∀ i, 0 < (p i).leadingCoeff)
    (ho : Orthonormal ℝ (fun i => M.evaluate (p i))) (i : Fin N) :
    p i = M.orthogonalPolynomial i := by
  -- Expand in the canonical orthonormal basis and eliminate every coefficient except the current degree.
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin N → Fin N → Prop)).induction with
  | h i ih =>
    let c := inner ℝ (M.polynomialBasis i) (M.evaluate (p i))
    have he : M.evaluate (p i) = c • M.polynomialBasis i := by
      have h := M.polynomialBasis.sum_repr' (M.evaluate (p i))
      rw [Finset.sum_eq_single i] at h
      · exact h.symm
      · intro j _ hji
        have hz : inner ℝ (M.polynomialBasis j) (M.evaluate (p i)) = 0 := by
          rcases lt_or_gt_of_ne hji with hj | hj
          · rw [← M.evaluate_orthogonalPolynomial j, ← ih j hj]
            exact ho.inner_eq_zero hji
          · exact M.polynomialBasis_orthogonal_lower (by rw [hdeg]; exact hj)
        rw [hz, zero_smul]
      · simp
    have hp : p i = c • M.orthogonalPolynomial i := by
      apply M.evaluate_injective (by rw [hdeg]; exact i.isLt)
        (lt_of_le_of_lt (natDegree_smul_le _ _) (by rw [(M.orthogonalPolynomial_degree i).1]; exact i.isLt))
      change M.evaluation (p i) = M.evaluation (c • M.orthogonalPolynomial i)
      rw [map_smul]
      change M.evaluate (p i) = c • M.evaluate (M.orthogonalPolynomial i)
      rw [M.evaluate_orthogonalPolynomial]
      exact he
    have hnorm : c^2 = 1 := by
      have h := ho.norm_eq_one i
      have hinner : inner ℝ (M.evaluate (p i)) (M.evaluate (p i)) = 1 := by
        rw [real_inner_self_eq_norm_sq, h]
        norm_num
      rw [he, inner_smul_left, inner_smul_right, M.polynomialBasis.inner_eq_one] at hinner
      simpa only [RCLike.conj_to_real, mul_one, ← pow_two] using hinner
    have hc : 0 < c := by
      have ht := congrArg (fun q : ℝ[X] => q.coeff i.val) hp
      rw [coeff_smul, smul_eq_mul] at ht
      rw [show (p i).coeff i.val = (p i).leadingCoeff by rw [← hdeg i, coeff_natDegree],
        show (M.orthogonalPolynomial i).coeff i.val = (M.orthogonalPolynomial i).leadingCoeff by
          rw [← (M.orthogonalPolynomial_degree i).1, coeff_natDegree]] at ht
      exact (mul_pos_iff_of_pos_right (M.orthogonalPolynomial_degree i).2).mp (ht ▸ hlc i)
    have hc1 : c = 1 := by nlinarith
    simpa only [hc1, one_smul] using hp

/-- Changing from any positive degree-graded input produces the canonical target polynomials.
Use: the comparison-chain Gram transformation is independent of the initial polynomial basis.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the earlier construction supplies exact degrees, positive leading coefficients
and orthonormality; uniqueness identifies each polynomial. -/
theorem changeOfMeasure_eq (p : Fin N → ℝ[X])
    (hdeg : ∀ i, (p i).natDegree = i.val) (hlc : ∀ i, 0 < (p i).leadingCoeff) (i : Fin N) :
    M.changeOfMeasure p i = M.orthogonalPolynomial i :=
  M.orthogonalPolynomial_unique _ (fun j => (M.changeOfMeasure_degree p hdeg hlc j).1)
    (fun j => (M.changeOfMeasure_degree p hdeg hlc j).2)
    (M.changeOfMeasure_orthonormal p hdeg hlc) i

end
end jacobi.Finite.DiscreteMeasure
