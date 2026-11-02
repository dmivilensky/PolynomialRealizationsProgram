import jacobi.Finite.Schur

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The explicit principal-block Schur residual is the actual Gram--Schmidt
residual in every row. Its complement is strictly positive, and its positive
square-root normalization is exactly the canonical normalized basis vector.
Source: uniqueness of orthogonal projection onto the preceding finite span.
Use: forms the principal Gram block with the correct dimension, including an empty first block.
-/
namespace jacobi.Finite.Gram
noncomputable section
open InnerProductSpace Matrix
open scoped BigOperators InnerProductSpace

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The indices strictly preceding a fixed polynomial degree.
Use: forms the principal Gram block with the correct dimension, including an empty first block.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def before (i : Fin N) (j : Fin i.val) : Fin N := ⟨j.val, j.isLt.trans i.isLt⟩

/-- The principal Schur residual equals the genuine Gram--Schmidt residual.
Use: identifies the inverse-block row formula with the actual new polynomial.
Article: jacobi, Theorem 2.1.
Proof: both residuals subtract a vector in the preceding span and are orthogonal
to that span. Their difference lies in the span and its orthogonal complement. -/
theorem residual_eq_gramSchmidt {f : Fin N → E} (hf : LinearIndependent ℝ f) (i : Fin N) :
    residual (fun j : Fin i.val => f (before i j)) (f i) = gramSchmidt ℝ f i := by
  -- Both residuals remove a vector in the preceding span and are orthogonal to that span.
  let g := fun j : Fin i.val => f (before i j)
  let K := Submodule.span ℝ (f '' Set.Iio i)
  have hg : LinearIndependent ℝ g := hf.comp _ (fun j k h => Fin.ext (congrArg (fun a : Fin N => a.val) h))
  have hsub : f i - gramSchmidt ℝ f i ∈ K := by
    nth_rw 1 [gramSchmidt_def'' ℝ f i]
    rw [add_sub_cancel_left]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    change gramSchmidt ℝ f j ∈ Submodule.span ℝ (f '' Set.Iio i)
    rw [← span_gramSchmidt_Iio ℝ f i]
    exact Submodule.subset_span ⟨j, Finset.mem_Iio.mp hj, rfl⟩
  have hres : f i - residual g (f i) ∈ K := by
    rw [residual, sub_sub_cancel]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨before i j, j.isLt, rfl⟩
  have hm : residual g (f i)-gramSchmidt ℝ f i ∈ K := by
    have h := K.sub_mem hsub hres
    convert h using 1
    abel
  have ho : ∀ v ∈ K, inner ℝ v (residual g (f i)-gramSchmidt ℝ f i) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, hj, rfl⟩ := hv
      rw [inner_sub_right]
      have hr := residual_orthogonal hg (f i) (⟨j.val, hj⟩ : Fin i.val)
      have hs := gramSchmidt_inv_triangular ℝ f hj
      change inner ℝ (f j) (residual g (f i)) = 0 at hr
      have hs' : inner ℝ (f j) (gramSchmidt ℝ f i) = 0 := by
        rw [real_inner_comm]
        exact hs
      rw [hr, hs', sub_self]
    | zero => simp
    | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
    | smul c v _ hv => simp only [inner_smul_left, hv, mul_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (ho _ hm))

/-- Every row complement is the strictly positive squared Gram residual norm.
Use: discharges the article's q_i>0 for actual degree-graded polynomial inputs.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: identify the residual with Gram--Schmidt and use independence. -/
theorem row_complement_pos {f : Fin N → E} (hf : LinearIndependent ℝ f) (i : Fin N) :
    0 < complement (fun j : Fin i.val => f (before i j)) (f i) := by
  have hg : LinearIndependent ℝ (fun j : Fin i.val => f (before i j)) :=
    hf.comp (before i) (fun j k h => Fin.ext (congrArg (fun a : Fin N => a.val) h))
  rw [← residual_norm_sq hg, residual_eq_gramSchmidt hf i]
  exact sq_pos_of_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero i hf))

/-- Positive Schur normalization gives exactly normalized Gram--Schmidt.
Use: is the complete row formula ψ_i=q_i^(-1/2)(ψ_i^0+Σc_ij ψ_j^0).
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: q_i is the squared residual norm, whose positive square root is its norm. -/
theorem normalized_row {f : Fin N → E} (hf : LinearIndependent ℝ f) (i : Fin N) :
    (Real.sqrt (complement (fun j : Fin i.val => f (before i j)) (f i)))⁻¹ •
      residual (fun j : Fin i.val => f (before i j)) (f i) = gramSchmidtNormed ℝ f i := by
  have hg : LinearIndependent ℝ (fun j : Fin i.val => f (before i j)) :=
    hf.comp (before i) (fun j k h => Fin.ext (congrArg (fun a : Fin N => a.val) h))
  rw [← residual_norm_sq hg, residual_eq_gramSchmidt hf i, Real.sqrt_sq (norm_nonneg _)]
  rfl

end
end jacobi.Finite.Gram
