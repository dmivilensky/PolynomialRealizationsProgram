import krylov.LinearAlgebra.Schur
import Mathlib.Data.Matrix.ColumnRowPartitioned
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, full-action endpoint construction.
Use: construct the minimal positive completion preserving an entire observed
operator action, including singular compressed blocks.
Source: finite-dimensional shorted positive operator construction, proved
directly from Albert69's generalized Schur criterion and the Penrose identities.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The actual Moore--Penrose inverse of a positive block is positive, including
its singular kernel.
Use: positivity of the constructed full-action endpoint requires no inverse gap.
Article: main_krylov, thm:radau.
Proof: the second Penrose identity writes the inverse as its own congruence
of the original positive block. -/
theorem positive_pseudoinverse (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.PosSemidef) :
    (pseudoinverse H hH.1).PosSemidef := by
  let B := chebyshev1.SpectralBasis.ofHermitian H hH.1
  have h := hH.conjTranspose_mul_mul_same (pseudoinverseInBasis B)
  change (pseudoinverseInBasis B).PosSemidef
  simpa only [conjTranspose_eq_transpose_of_trivial,(pseudoinverse_isSymm B).eq,
    pseudoinverse_penrose_right] using h

/-- The minimal positive form consistent with an entire measured column action.
Use: construct physical Krein endpoints without postulating their existence.
Article: main_krylov, thm:radau, full-action constraints.
Proof: lift the true compressed Moore--Penrose inverse through the observed
physical action columns. -/
def shortedForm (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (S : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let hH := hM.conjTranspose_mul_mul_same S
  (M*S)*pseudoinverse (Sᵀ*M*S)
    (by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.1)*(M*S)ᵀ

/-- The explicit shorted form is positive, lies below the actual original
positive matrix and preserves its entire physical action on the stored window.
Use: all three properties of the full-action endpoint are proved together,
including singular compressed blocks and arbitrary old-column dependencies.
Article: main_krylov, thm:radau, full-action endpoint construction.
Proof: compress the original positive form by [I S]. The genuine generalized
Schur criterion supplies both its range condition and its positive remainder;
the range condition and Penrose inverse give exact action preservation. -/
theorem shorted_form_properties (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (S : Matrix (Fin n) (Fin p) ℝ) :
    (shortedForm M hM S).PosSemidef ∧ (M-shortedForm M hM S).PosSemidef ∧
      shortedForm M hM S*S=M*S := by
  let H := Sᵀ*M*S
  have hH : H.PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hM.conjTranspose_mul_mul_same S
  let P := pseudoinverse H hH.1
  have hP : P.IsSymm := pseudoinverse_isSymm (chebyshev1.SpectralBasis.ofHermitian H hH.1)
  have hcross : (Sᵀ*M)ᵀ=M*S := by
    simp only [transpose_mul,transpose_transpose,hM.1.isSymm.eq]
  have hblock : (fromBlocks M (Sᵀ*M)ᵀ (Sᵀ*M) H).PosSemidef := by
    have h := hM.conjTranspose_mul_mul_same (fromCols (1 : Matrix (Fin n) (Fin n) ℝ) S)
    simpa only [conjTranspose_eq_transpose_of_trivial,transpose_fromCols,transpose_one,
      fromRows_mul,mul_fromCols,fromCols_fromRows_eq_fromBlocks,
      Matrix.one_mul,Matrix.mul_one,hcross,H] using h
  obtain ⟨hr,hrem⟩ := (generalized_schur_iff M H hH (Sᵀ*M)).mp hblock
  have he : shortedForm M hM S=(M*S)*P*(M*S)ᵀ := rfl
  refine ⟨?_,?_,?_⟩
  · rw [he]
    simpa only [conjTranspose_eq_transpose_of_trivial,transpose_transpose] using
      (positive_pseudoinverse H hH).conjTranspose_mul_mul_same (M*S)ᵀ
  · simpa only [he,hcross,transpose_mul,transpose_transpose,hM.1.isSymm.eq] using hrem
  · have hsolve : H*P*(Sᵀ*M)=Sᵀ*M :=
      (pseudoinverse_range_iff (chebyshev1.SpectralBasis.ofHermitian H hH.1) (Sᵀ*M)).mp hr
    have ht := congrArg Matrix.transpose hsolve
    simp only [transpose_mul,transpose_transpose,hM.1.isSymm.eq,hH.1.isSymm.eq,hP.eq] at ht
    rw [he]
    calc
      (M*S)*P*(M*S)ᵀ*S=(M*S)*P*H := by
        simp only [transpose_mul,hM.1.isSymm.eq,Matrix.mul_assoc,H]
      _=M*S := by simpa only [Matrix.mul_assoc] using ht

end
end krylov.Completion
