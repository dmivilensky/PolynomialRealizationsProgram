import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Injective finite coordinate inclusion and genuine zero extension preserve
both the Euclidean squared norm and the complete matrix quadratic form.
The full physical-prefix lower bound therefore applies to every smaller
principal section with exactly the same positive constant.
Use: targetGram_submatrix_coercive transfers the actual full half-prefix bound to every principal Gram section used by Cholesky.
-/
namespace jacobi.Analysis
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f:ι→κ) (hf:Function.Injective f)
include hf

/-- Genuine zero extension through an injective finite coordinate map
preserves the Euclidean squared norm exactly.
Use: targetGram_submatrix_coercive transfers the actual full half-prefix
bound to every principal Gram section used by Cholesky.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the original coordinates retain their actual values and all
coordinates outside the image have exactly zero value. -/
theorem zeroExtension_norm_sq (v:ι→ℝ) :
    (∑ j:κ, (Function.extend f v (fun _ => 0) j)^2)=∑ i:ι, (v i)^2 := by
  symm
  apply Fintype.sum_of_injective f hf
  · intro j hj
    rw [Function.extend_apply' v (fun _ => (0:ℝ)) j hj]
    norm_num
  · intro i
    rw [hf.extend_apply]

/-- Genuine finite zero extension preserves the complete principal
matrix form, with all original cross terms and coefficient values.
Use: the true uniform Gram gap is inherited by the original principal
blocks whose inverses define the actual Cholesky rows.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: transport each finite index through the genuine injection; each
omitted row or column contains a zero extended vector coordinate. -/
theorem zeroExtension_quadratic (A:κ→κ→ℝ) (v:ι→ℝ) :
    (∑ i:κ,∑ j:κ, A i j*Function.extend f v (fun _ => 0) i*
      Function.extend f v (fun _ => 0) j)=
      ∑ i:ι,∑ j:ι, A (f i) (f j)*v i*v j := by
  -- Every coordinate outside the actual image contributes zero in either matrix index.
  let w := Function.extend f v (fun _ => (0:ℝ))
  have hw (i:ι) : w (f i)=v i := hf.extend_apply _ _ i
  have hz (j:κ) (hj:j∉Set.range f) : w j=0 := Function.extend_apply' _ _ j hj
  have hinner (i:κ) : (∑ j:ι, A i (f j)*w i*v j) = ∑ j:κ, A i j*w i*w j := by
    apply Fintype.sum_of_injective f hf
    · intro j hj
      rw [hz j hj,mul_zero]
    · intro j
      rw [hw]
  symm
  calc
    _ = ∑ i:ι,∑ j:ι, A (f i) (f j)*w (f i)*v j := by simp only [hw]
    _ = ∑ i:ι,∑ j:κ, A (f i) j*w (f i)*w j := by simp_rw [hinner]
    _ = ∑ i:κ,∑ j:κ, A i j*w i*w j := by
      apply Fintype.sum_of_injective f hf (fun i => ∑ j:κ, A (f i) j*w (f i)*w j)
        (fun i => ∑ j:κ, A i j*w i*w j)
      · intro i hi
        simp only [hz i hi,mul_zero,zero_mul,Finset.sum_const_zero]
      · intro i
        rfl

end
end jacobi.Analysis
