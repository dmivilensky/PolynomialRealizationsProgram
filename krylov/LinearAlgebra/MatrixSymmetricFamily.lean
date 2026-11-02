import krylov.Reference.CanonicalSteps
set_option autoImplicit false
/-!
Article: main_krylov, thm:I and apA:galerkin(e), genuine matrix uncertainty dictionary.
Use: transfer exact attained operator uncertainty maxima to the original
real symmetric canonical matrix budgets without weakening the scenario class.
Source: the reused genuine Euclidean star-algebra equivalence is isometric
for the original spectral matrix norm.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*}

/-- Every actual value set over independent symmetric canonical matrix budgets
is exactly its true self-adjoint-operator value set.
Use: source sharp constants retain original matrix scenarios and attaining
matrices, rather than just a larger abstract operator uncertainty class.
Article: main_krylov, thm:I; apA:galerkin(e).
Proof: the true Euclidean star-algebra equivalence maps every real symmetric
matrix to a self-adjoint operator and preserves its spectral norm. Its actual
inverse constructs the reverse matrix family, with the same genuine budget and output. -/
theorem symmetric_matrix_family_values (I : Finset ι) (omega : ι → ℝ)
    (f : (ι → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) → ℝ) :
    {z : ℝ | ∃ M : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ i∈I,(M i).IsSymm ∧ ‖M i‖≤omega i) ∧ z=f (fun i => cgOperator (M i))}=
    {z : ℝ | ∃ T : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ i∈I,IsSelfAdjoint (T i) ∧ ‖T i‖≤omega i) ∧ z=f T} := by
  ext z
  constructor
  · rintro ⟨M,hM,rfl⟩
    refine ⟨fun i => cgOperator (M i),?_,rfl⟩
    intro i hi
    constructor
    · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hM i hi).1)
    · exact (hM i hi).2
  · rintro ⟨T,hT,rfl⟩
    let M := fun i => (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.symm (T i)
    have he (i : ι) : cgOperator (M i)=T i :=
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply (T i)
    refine ⟨M,?_,?_⟩
    · intro i hi
      constructor
      · apply Matrix.isHermitian_iff_isSymm.mp
        apply Matrix.isSymmetric_toEuclideanLin_iff.mp
        change (cgOperator (M i)).toLinearMap.IsSymmetric
        rw [he]
        exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hT i hi).1
      · rw [← Matrix.l2_opNorm_toEuclideanCLM]
        change ‖cgOperator (M i)‖≤omega i
        rw [he]
        exact (hT i hi).2
    · congr 1
      exact (funext he).symm

end
end krylov.LinearAlgebra
