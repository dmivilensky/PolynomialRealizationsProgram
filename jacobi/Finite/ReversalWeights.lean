import jacobi.Finite.Persymmetric

/-!
Article: jacobi, Proposition 1.1.
Physical reversal of eigenvectors gives the spectral weights of the reversed
matrix. The endpoint cofactor identity from chebyshev1 then gives the exact
reciprocal-weight involution on the entire positive simplex.
Source: the finite spectral theorem and the endpoint cofactor formula.
Use: identifies the first weights after reversal with the old last weights.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reverse physical coordinates, keeping the spectral column order unchanged.
Use: identifies the first weights after reversal with the old last weights.
Article: jacobi, Proposition 1.1.
Proof: orthogonality and diagonalization are invariant under the row permutation. -/
def reversedBasis {N : ℕ} (J : Jacobi N) (B : SpectralBasis J.matrix) :
    SpectralBasis (reverse J).matrix where
  Q i j := B.Q i.rev j
  eigenvalues := B.eigenvalues
  transpose_mul := by
    ext i j
    change (∑ k : Fin N, B.Q k.rev i * B.Q k.rev j) = (1 : Matrix (Fin N) (Fin N) ℝ) i j
    exact (Equiv.sum_comp Fin.revPerm (fun k => B.Q k i * B.Q k j)).trans
      (congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) B.transpose_mul)
  mul_transpose := by
    ext i j
    have h := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i.rev j.rev) B.mul_transpose
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.rev_injective.eq_iff] using h
  diagonalize := by
    rw [reverse_matrix]
    ext i j
    change (∑ k : Fin N, (∑ l : Fin N, B.Q l.rev i * J.matrix l.rev k.rev) * B.Q k.rev j) =
      (Matrix.diagonal B.eigenvalues) i j
    calc
      _ = ∑ k : Fin N, (∑ l : Fin N, B.Q l i * J.matrix l k.rev) * B.Q k.rev j := by
        apply Finset.sum_congr rfl
        intro k _
        exact congrArg (fun t : ℝ => t * B.Q k.rev j)
          (Equiv.sum_comp Fin.revPerm (fun l => B.Q l i * J.matrix l k.rev))
      _ = ∑ k : Fin N, (∑ l : Fin N, B.Q l i * J.matrix l k) * B.Q k j :=
        Equiv.sum_comp Fin.revPerm (fun k => (∑ l : Fin N, B.Q l i * J.matrix l k) * B.Q k j)
      _ = _ := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) B.diagonalize

/-- Reversal of an element of the actual polynomial fibre.
Use: the geometric involution transported to logarithmic spectral coordinates.
Article: jacobi, Proposition 1.1.
-/
def reverseFiber {N : ℕ} {p : Polynomial ℝ} (J : Fiber N p) : Fiber N p :=
  ⟨reverse J.val, reverse_mem_fiber J.property⟩

/-- The exact reversed first-site probability at each prescribed spectral node.
Use: proves that logarithmic coordinates turn reversal into negation.
Article: jacobi, Proposition 1.1.
Proof: compare the chosen basis with the physically reversed basis, then solve
 the already proved endpoint cofactor product identity for the last weight. -/
theorem spectralWeights_reverse {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial)
    (k : Fin (n+1)) :
    (spectralWeights S (reverseFiber J)).val k = J.val.data.couplingProduct 1 n /
      ((spectralWeights S J).val k * (S.polynomial.derivative.eval (S.value k))^2) := by
  -- Physical row reversal turns the new first weight into the old last weight; solve the endpoint product identity.
  let B := orderedBasis S J.val J.property
  let C := orderedBasis S (reverse J.val) (reverse_mem_fiber J.property)
  have he : B.eigenvalues = S.value := orderedBasis_values S J.val J.property
  have hc : C.eigenvalues = B.eigenvalues :=
    (orderedBasis_values S _ _).trans he.symm
  have hi : Function.Injective B.eigenvalues := he.symm ▸ S.strictAnti.injective
  have hw := basis_weights_independent (reverse J.val) C (reversedBasis J.val B) hc
    (hc.symm ▸ hi) k
  have hp : J.val.data.leading (n+1) = S.polynomial := by
    rw [JacobiData.leading, J.val.data.block_eq_charpoly J.val.coupling_nonneg]
    exact J.property.2
  have hprod := J.val.data.spectral_endpoint_product B J.val.coupling_nonneg hi k
  rw [hp, he] at hprod
  change C.weight 0 k = _
  rw [hw]
  change B.weight (Fin.last n) k = _
  apply (eq_div_iff (mul_ne_zero ((spectralWeights S J).property.1 k).ne'
    (pow_ne_zero 2 (S.derivative_ne_zero k)))).mpr
  change B.weight (Fin.last n) k * (B.weight 0 k * _) = _
  nlinarith [hprod]

/-- The constant in the reciprocal-weight formula is strictly positive.
Use: division and normalization in the logarithmic reversal formula are legitimate.
Article: jacobi, Proposition 1.1.
Proof: it is the product of the strictly positive internal squared couplings. -/
theorem reversal_constant_pos {n : ℕ} {p : Polynomial ℝ} (J : Fiber (n+1) p) :
    0 < J.val.data.couplingProduct 1 n := by
  unfold JacobiData.couplingProduct
  apply Finset.prod_pos
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact J.property.1 (1+i) (by omega) (by omega)

end
end jacobi.Finite
