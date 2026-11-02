import jacobi.Jacobi.SturmGreen

/-!
Article: jacobi, Proposition A.1.
The actual degree-graded Jacobi family is orthogonal to every lower-degree
polynomial for its literal weight, throughout alpha,beta>-1. The community
polynomial-sequence span theorem supplies all tests without a duplicate
basis construction.
Source: Jacobi Sturm orthogonality and Polynomial.Sequence.span_degreeLT.
Use: the kernel contains the span of all earlier Jacobi polynomials.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Integration against one actual Jacobi polynomial and its genuine weight, as a real linear functional on all polynomial tests.
Use: the kernel contains the span of all earlier Jacobi polynomials.
Article: jacobi, Proposition A.1.
-/
def weightedIntegralMap (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun q := ∫ t in (0:ℝ)..1,weight a b t*((shiftedPolynomial a b n).eval t*q.eval t)
  map_add' p q := by
    -- Convergence is proved for both summands before applying linearity of integration.
    simp only [eval_add,mul_add]
    exact intervalIntegral.integral_add
      (weight_mul_integrable ha hb ((shiftedPolynomial a b n).continuous.mul p.continuous))
      (weight_mul_integrable ha hb ((shiftedPolynomial a b n).continuous.mul q.continuous))
  map_smul' c q := by
    simp only [eval_smul,smul_eq_mul]
    have he : (fun t => weight a b t*((shiftedPolynomial a b n).eval t*(c*q.eval t)))=
        fun t => c*(weight a b t*((shiftedPolynomial a b n).eval t*q.eval t)) := by funext t; ring
    rw [he,intervalIntegral.integral_const_mul]
    rfl

/-- The actual shifted Jacobi polynomial is orthogonal to every lower-degree real polynomial.
Use: proves the complete location and simplicity of its finite zero set.
Article: jacobi, Proposition A.1.
Proof: the community degree-graded polynomial-sequence theorem says
that the preceding Jacobi polynomials span every lower-degree polynomial.
Their actual weighted integrals vanish by Sturm orthogonality, so that
span lies in the kernel of the genuine integration functional. -/
theorem shiftedPolynomial_orthogonal_lower {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} {q : Polynomial ℝ} (hq : q.natDegree<n) :
    ∫ t in (0:ℝ)..1,weight a b t*((shiftedPolynomial a b n).eval t*q.eval t)=0 := by
  -- Reuse the actual community span theorem rather than redoing triangular polynomial elimination.
  let S := shiftedSequence a b ha hb
  let L := weightedIntegralMap a b ha hb n
  have hunit : ∀ i<n,IsUnit (S i).leadingCoeff := by
    intro i _
    apply isUnit_iff_ne_zero.mpr
    exact leadingCoeff_ne_zero.mpr (shiftedPolynomial_ne_zero ha hb i)
  have hspan : q∈Submodule.span ℝ (S '' Iio n) := by
    rw [S.span_degreeLT hunit,Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hq)
  have hker : Submodule.span ℝ (S '' Iio n)≤LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro p ⟨i,hi,rfl⟩
    change (∫ t in (0:ℝ)..1,weight a b t*
      ((shiftedPolynomial a b n).eval t*(shiftedPolynomial a b i).eval t))=0
    exact shiftedPolynomial_orthogonal ha hb (Nat.ne_of_gt hi)
  exact hker hspan

end
end jacobi.Jacobi
