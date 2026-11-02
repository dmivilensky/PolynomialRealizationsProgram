import jacobi.Counterexample.SwappedChain

/-!
Article: jacobi, Proposition 6.1.
The original explicit Jacobi chain has exactly the printed Green matrix
and constant diagonal H/kappa. Its characteristic polynomial does not
vanish at one, as proved from the actual inverse product before using
the full-fibre logarithmic derivative.
Use: alternating_inverse_product and constantDriftChain_green compute the unchanged source inverse exactly.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix jacobi.Finite chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The original alternating-sign conjugation is its own genuine matrix inverse.
Use: alternating_inverse_product and constantDriftChain_green compute the unchanged source inverse exactly.
Article: jacobi, Proposition 6.1.
Proof: its two diagonal factors multiply to the square of each original alternating sign, which equals one. -/
theorem alternating_matrix_sq (N:ℕ) : alternatingMatrix N*alternatingMatrix N=1 := by
  rw [alternatingMatrix,Matrix.diagonal_mul_diagonal]
  simp only [← pow_two,alternating_sq,Matrix.diagonal_one]

/-- The original alternating conjugation of a positive matrix times the conjugation of its true inverse is exactly the identity.
Use: constantDriftChain_green applies nonsingular inverse scaling only after this genuine product proves its determinant premise.
Article: jacobi, Proposition 6.1.
Proof: associate the two interior alternating factors, cancel D^2=I,
then cancel the actual positive matrix with its independently defined
nonsingular inverse and cancel the remaining outer D^2. -/
theorem alternating_inverse_product {N:ℕ} {Y:Matrix (Fin N) (Fin N) ℝ} (hY:Y.PosDef) :
    (alternatingMatrix N*Y*alternatingMatrix N)*
      (alternatingMatrix N*Y⁻¹*alternatingMatrix N)=1 := by
  -- Both inverses concern the same original finite matrix.
  calc
    _ = alternatingMatrix N*Y*(alternatingMatrix N*alternatingMatrix N)*Y⁻¹*alternatingMatrix N := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [alternating_matrix_sq,Matrix.mul_one,Matrix.mul_assoc (alternatingMatrix N) Y Y⁻¹,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit),
        Matrix.mul_one,alternating_matrix_sq]

/-- The actual attaining chain has exactly the printed original Green matrix.
Use: constantDriftChain_diagonal gives the constant original resolvent diagonal used in its full-fibre minimum proof.
Article: jacobi, Proposition 6.1.
Proof: the actual pencil is H^(-1)*D*Y'*D. The verified inverse product
fixes its true nonsingular inverse. The community scalar inverse rule
then cancels the original nonzero H with its inverse. -/
theorem constantDriftChain_green {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    (constantDriftChain d l N H).green=
      H • (alternatingMatrix N*(swappedGram d l N)⁻¹*alternatingMatrix N) := by
  -- Scaling is applied only to a matrix whose actual inverse has already been checked.
  have hprod := alternating_inverse_product (swapped_posDef d l hk hd)
  have hdet := Matrix.isUnit_det_of_right_inverse hprod
  let _ : Invertible (H⁻¹) := invertibleOfNonzero (inv_ne_zero hH.ne')
  rw [Jacobi.green,constantDriftChain_pencil d l hk hH hdiag hlower hd,
    Matrix.inv_smul _ _ hdet,invOf_eq_inv,inv_inv,Matrix.inv_eq_right_inv hprod]

/-- Every actual source Green diagonal entry is the exact constant H/kappa.
Use: constantDriftChain_minimum evaluates the true finite energy and attains Cauchy--Schwarz on the complete original fibre.
Article: jacobi, Proposition 6.1.
Proof: evaluate the proved actual Green conjugation on its diagonal.
The original alternating signs have square one, and the genuine swapped
inverse diagonal has already been proved equal to 1/kappa. -/
theorem constantDriftChain_diagonal {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hl:l 0=0) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) (i:Fin N) :
    (constantDriftChain d l N H).green i i=H/kappa := by
  -- The diagonal belongs to the literal original inverse in Jacobi.energy.
  rw [constantDriftChain_green d l hk hH hdiag hlower hd]
  simp only [Matrix.smul_apply,smul_eq_mul,alternatingMatrix,Matrix.diagonal_mul,
    Matrix.mul_diagonal,swapped_inverse_diagonal d l hk hl hd]
  calc
    _ = H*((-1:ℝ)^i.val)^2/kappa := by ring
    _ = H/kappa := by rw [alternating_sq,mul_one]

/-- The actual original attaining characteristic polynomial is nonzero at the resolvent endpoint.
Use: constantDriftChain_minimum applies the full original polynomial logarithmic derivative with its determinant premise discharged.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the checked original conjugation product proves its determinant
nonzero; multiplication by the genuine nonzero H^(-1) preserves this.
The community characteristic evaluation identifies p(1) with that determinant. -/
theorem constantDriftChain_endpoint_ne {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    (constantDriftChain d l N H).matrix.charpoly.eval 1≠0 := by
  -- Endpoint nonvanishing is obtained from the original matrix, rather than supplied to the optimization theorem.
  have hprod := alternating_inverse_product (swapped_posDef d l hk hd)
  have hone : Matrix.scalar (Fin N) (1:ℝ)=1 := by ext i j; simp
  rw [Matrix.eval_charpoly,hone,constantDriftChain_pencil d l hk hH hdiag hlower hd,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hH.ne')) (Matrix.det_ne_zero_of_right_inverse hprod)

end
end jacobi.Counterexample
