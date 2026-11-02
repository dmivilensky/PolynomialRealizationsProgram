import jacobi.Finite.Gram

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The principal Gram linear system, its Schur complement and the normalized new
vector are proved for arbitrary finite input vectors. For polynomial evaluation
vectors this is exactly the row formula c = −Gᵢ,< G<⁻¹ and its normalization q.
Source: finite orthogonal projection and the Schur complement identity.
Use: their negatives are the article's row coefficients cᵢⱼ.
-/

namespace jacobi.Finite.Gram
noncomputable section
open Matrix
open scoped InnerProductSpace BigOperators

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Solve the principal Gram system for the projection coefficients.
Use: their negatives are the article's row coefficients cᵢⱼ.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def coefficients (f : Fin N → E) (v : E) : Fin N → ℝ :=
  (Matrix.gram ℝ f)⁻¹ *ᵥ (fun i => inner ℝ (f i) v)

/-- Remove the projection onto the preceding polynomial evaluation vectors.
Use: its normalization is the next orthonormal polynomial vector.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def residual (f : Fin N → E) (v : E) : E :=
  v - ∑ i, coefficients f v i • f i

/-- The scalar Schur complement in the augmented Gram matrix.
Use: the exact positive normalization q in the article's row formula.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def complement (f : Fin N → E) (v : E) : ℝ :=
  inner ℝ v v - ∑ i, coefficients f v i * inner ℝ (f i) v

/-- The explicit inverse solves the principal Gram linear system.
Use: proves all orthogonality conditions for the next vector.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: independent inputs have an invertible positive definite Gram matrix. -/
theorem coefficients_system {f : Fin N → E} (hf : LinearIndependent ℝ f) (v : E) :
    Matrix.gram ℝ f *ᵥ coefficients f v = fun i => inner ℝ (f i) v := by
  have hd := (Matrix.posDef_gram_of_linearIndependent hf).det_pos
  rw [coefficients, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd.ne'), Matrix.one_mulVec]

/-- The Schur residual is orthogonal to every preceding input.
Use: identifies the row formula as Gram--Schmidt, rather than merely an algebraic candidate.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: expand the inner product and substitute the principal Gram system. -/
theorem residual_orthogonal {f : Fin N → E} (hf : LinearIndependent ℝ f) (v : E) (i : Fin N) :
    inner ℝ (f i) (residual f v) = 0 := by
  have h := congrFun (coefficients_system hf v) i
  simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply] at h
  simp only [residual, inner_sub_right, inner_sum, inner_smul_right]
  rw [show (∑ j, coefficients f v j * inner ℝ (f i) (f j)) = inner ℝ (f i) v by
    simpa only [mul_comm] using h, sub_self]

/-- The Schur complement is the squared norm of the actual orthogonal residual.
Use: gives positivity and the correct normalization factor without extra hypotheses.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the removed projection is orthogonal to the residual; expand the remaining pairing. -/
theorem residual_norm_sq {f : Fin N → E} (hf : LinearIndependent ℝ f) (v : E) :
    ‖residual f v‖^2 = complement f v := by
  -- The removed projection is orthogonal to the residual, so the squared norm reduces to one pairing.
  have hz : inner ℝ (∑ i, coefficients f v i • f i) (residual f v) = 0 := by
    simp only [sum_inner, inner_smul_left, residual_orthogonal hf v,
      mul_zero, Finset.sum_const_zero]
  calc
    _ = inner ℝ (residual f v) (residual f v) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ v (residual f v) := by
      nth_rw 1 [residual]
      rw [inner_sub_left, hz, sub_zero]
    _ = complement f v := by
      simp only [residual, complement, inner_sub_right, inner_sum, inner_smul_right]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm v (f i)]

/-- A genuinely new input has a strictly positive Schur complement.
Use: discharges q > 0 for every row of the polynomial change of measure.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: a zero residual would express the new input in the preceding span. -/
theorem complement_pos {f : Fin N → E} (hf : LinearIndependent ℝ f) {v : E}
    (hv : v ∉ Submodule.span ℝ (Set.range f)) : 0 < complement f v := by
  -- A vanishing residual would place the new vector in the preceding span, contradicting its independence.
  rw [← residual_norm_sq hf v]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hv
  have he : v = ∑ i, coefficients f v i • f i := sub_eq_zero.mp hz
  rw [he]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- Column-system coefficients equal the row multiplication used in the printed formula.
Use: reads the explicit Schur coefficients as c=-G_i,< G_<⁻¹ without an orientation assumption.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the real Gram matrix and its inverse are symmetric; transpose the entrywise sum. -/
theorem coefficients_row (f : Fin N → E) (v : E) (i : Fin N) :
    coefficients f v i = ∑ j, inner ℝ v (f j) * (Matrix.gram ℝ f)⁻¹ j i := by
  -- Symmetry of the inverse turns the column-system sum into the printed row sum.
  have hs : (Matrix.gram ℝ f).IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    exact real_inner_comm _ _
  simp only [coefficients, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [hs.inv.apply i j, real_inner_comm]
  ring


end
end jacobi.Finite.Gram
