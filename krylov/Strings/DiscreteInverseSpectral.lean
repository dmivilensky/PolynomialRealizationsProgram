import krylov.Strings.DiscreteInverseString
import krylov.Strings.DiscreteChristoffel
import krylov.Strings.DiscreteGershgorin

/-!
Article: `main_krylov`, `apC:lem:stieltjes(b)`.
The actual inverse string has an explicitly constructed complete physical
eigenbasis with exactly the prescribed nodes and boundary probabilities.
Its canonical polynomials and Christoffel kernels are identified with the
same input measure, and its genuine norm is the largest prescribed node.
-/

namespace krylov.Strings.DiscreteInverse
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- Actual physical orthogonal diagonalization of the inverse string, with
its prescribed original node ordering and its original spectral weights. -/
def basis (hnode : ∀ i,0≤M.node i) : SpectralBasis (string M hnode).operator where
  Q := (string M hnode).signMatrix*M.reconstructedBasis.Q
  eigenvalues := M.node
  transpose_mul := by
    rw [transpose_mul, (string M hnode).signMatrix_transpose]
    calc
      _ = M.reconstructedBasis.Qᵀ*((string M hnode).signMatrix*(string M hnode).signMatrix)*
          M.reconstructedBasis.Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(string M hnode).signMatrix_sq, Matrix.mul_one, M.reconstructedBasis.transpose_mul]
  mul_transpose := by
    rw [transpose_mul, (string M hnode).signMatrix_transpose]
    calc
      _ = (string M hnode).signMatrix*(M.reconstructedBasis.Q*M.reconstructedBasis.Qᵀ)*
          (string M hnode).signMatrix := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [M.reconstructedBasis.mul_transpose, Matrix.mul_one, (string M hnode).signMatrix_sq]
  diagonalize := by
    rw [transpose_mul, (string M hnode).signMatrix_transpose]
    calc
      _ = M.reconstructedBasis.Qᵀ*((string M hnode).signMatrix*(string M hnode).operator*
          (string M hnode).signMatrix)*M.reconstructedBasis.Q := by simp only [Matrix.mul_assoc]
      _ = diagonal M.node := by
        rw [← DiscreteString.positiveOperator, string_positiveOperator]
        exact M.reconstructedBasis.diagonalize

/-- Every prescribed weight is the true first-site weight of the actual
inverse physical operator, with no assumed spectral identity. -/
theorem basis_weight (hnode : ∀ i,0≤M.node i) (k : Fin (N+1)) :
    (basis M hnode).weight 0 k=M.weight k := by
  change ((string M hnode).signMatrix*M.reconstructedBasis.Q) 0 k^2=M.weight k
  simp only [DiscreteString.signMatrix, Matrix.diagonal_mul, Fin.val_zero, pow_zero, one_mul]
  have h := M.reconstructed_weight (Nat.succ_pos N) k
  have hzero : (⟨0, Nat.succ_pos N⟩ : Fin (N+1))=0 := by apply Fin.ext; simp
  rw [hzero] at h
  exact h

/-- The actual inverse string norm is exactly the largest prescribed
spectral support node, including measures with a zero atom. -/
theorem spectralRadius_isGreatest (hnode : ∀ i,0≤M.node i) :
    IsGreatest (Set.range M.node) (string M hnode).spectralRadius :=
  (string M hnode).spectralRadius_isGreatest (basis M hnode)

/-- The input canonical orthogonal polynomials are exactly the signed
mass-normalized actual physical position polynomials of the inverse string. -/
theorem orthogonalPolynomial_eq (hnode : ∀ i,0≤M.node i) (i : Fin (N+1)) :
    M.orthogonalPolynomial i=
      C ((-1 : ℝ)^i.val*Real.sqrt ((string M hnode).mass i.val))*
        (string M hnode).φPolynomial i.val := by
  rw [← normalizedLeading_eq_orthogonalPolynomial M i, ← string_jacobi M hnode]
  exact (string M hnode).normalizedLeading_physical i

/-- The exact actual input Christoffel diagonal equals the accumulated
physical energy of the same inverse string prefix. -/
theorem christoffelKernel_eq (hnode : ∀ i,0≤M.node i) (m : ℕ) (hm : m≤N) :
    krylov.Reference.christoffelKernel M m (-1)=(string M hnode).K m := by
  have hpoly (i : Fin (N+1)) :
      ((M.orthogonalPolynomial i).eval (-1))^2=
        (string M hnode).mass i.val*(string M hnode).φ i.val^2 := by
    rw [orthogonalPolynomial_eq M hnode i, eval_mul, eval_C,
      ((string M hnode).polynomialState_eval_neg_one i.val).1, mul_pow, mul_pow,
      alternating_sq, Real.sq_sqrt ((string M hnode).mass_pos i.val (by omega)).le, one_mul]
  rw [krylov.Reference.christoffelKernel]
  simp_rw [hpoly]
  rw [DiscreteString.sum_physical_prefix m hm
    (fun k ↦ (string M hnode).mass k*(string M hnode).φ k^2),
    (string M hnode).K_eq_sum]

/-- The actual inverse physical position polynomial has the source's
precise normalization by the nonzero canonical polynomial value at zero. -/
theorem physicalPolynomial_eq (hnode : ∀ i,0≤M.node i) (i : Fin (N+1)) :
    (string M hnode).φPolynomial i.val=
      C ((M.orthogonalPolynomial i).eval 0)⁻¹*M.orthogonalPolynomial i := by
  have hid := orthogonalPolynomial_eq M hnode i
  have hvalue : (M.orthogonalPolynomial i).eval 0=
      (-1 : ℝ)^i.val*Real.sqrt ((string M hnode).mass i.val) := by
    rw [hid, eval_mul, eval_C, ((string M hnode).polynomialState_eval_zero i.val).1, mul_one]
  have hc : (M.orthogonalPolynomial i).eval 0≠0 := by
    rw [hvalue]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Real.sqrt_pos.mpr ((string M hnode).mass_pos i.val (by omega))).ne'
  rw [hvalue, hid, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by rwa [← hvalue]), C_1, one_mul]

/-- Full constructive finite inverse dictionary needed by the design
asymptotics: an actual positive string with the prescribed support norm
and all actual exterior Christoffel energies. -/
theorem exists_string (hnode : ∀ i,0≤M.node i) :
    ∃ S : DiscreteString N,
      IsGreatest (Set.range M.node) S.spectralRadius ∧
      (∀ m≤N, krylov.Reference.christoffelKernel M m (-1)=S.K m) ∧
      (∃ B : SpectralBasis S.operator, B.eigenvalues=M.node ∧ ∀ k,B.weight 0 k=M.weight k) := by
  exact ⟨string M hnode, spectralRadius_isGreatest M hnode, christoffelKernel_eq M hnode,
    basis M hnode, rfl, basis_weight M hnode⟩

end
end krylov.Strings.DiscreteInverse
