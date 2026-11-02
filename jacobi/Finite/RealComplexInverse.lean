import jacobi.Finite.ComplexResolvent

/-!
Article: jacobi, Corollary C.6.
Complexifying the genuine real matrix inverse preserves every entry,
including the totalized singular case. This identifies Theorem C.5's
real-shift energy with the original ordinary real objective.
Use: real_shifted_inverse and the real shifted candidate energy limit reuse Theorem C.5 verbatim.
-/
namespace jacobi.Finite
noncomputable section
open Matrix

/-- The complexification of the actual real inverse is the inverse of the same complexified matrix.
Use: real_shifted_inverse and the real shifted candidate energy limit reuse Theorem C.5 verbatim.
Article: jacobi, Corollary C.6.
Source: the adjugate/determinant formula for a matrix inverse.
Proof: both adjugate and determinant commute with the genuine scalar
homomorphism, and ordinary real inversion commutes with complexification. -/
theorem real_complex_inverse {N:ℕ} (A:Matrix (Fin N) (Fin N) ℝ) :
    (A⁻¹).map Complex.ofRealHom=(A.map Complex.ofRealHom)⁻¹ := by
  -- Adjugate and determinant are transported before simplifying the actual scalar inverse.
  have hd : (A.map Complex.ofRealHom).det=(A.det:ℂ) := (Complex.ofRealHom.map_det A).symm
  have ha : (A.map Complex.ofRealHom).adjugate=A.adjugate.map Complex.ofRealHom :=
    (Complex.ofRealHom.map_adjugate A).symm
  rw [Matrix.inv_def,Matrix.inv_def,hd,ha]
  ext i j
  simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
  change ((A.det⁻¹*A.adjugate i j:ℝ):ℂ)=(A.det:ℂ)⁻¹*(A.adjugate i j:ℂ)
  push_cast
  rfl

/-- The original real shifted inverse agrees entry by entry with its genuine complex resolvent.
Use: real-shift finite costs and their true candidate limits use the same matrix as Theorem C.5.
Article: jacobi, Corollary C.6.
Proof: complexify the actual affine pencil and apply the exact inverse identity. -/
theorem real_shifted_inverse {N:ℕ} (A:Matrix (Fin N) (Fin N) ℝ) (z:ℝ) :
    ((z • (1:Matrix (Fin N) (Fin N) ℝ)-A)⁻¹).map Complex.ofRealHom=
      ((z:ℂ) • (1:Matrix (Fin N) (Fin N) ℂ)-A.map Complex.ofRealHom)⁻¹ := by
  rw [real_complex_inverse]
  congr 1
  ext i j
  simp only [Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply]
  change ((z*(if i=j then (1:ℝ) else 0)-A i j:ℝ):ℂ)=_
  push_cast
  split_ifs <;> simp

end
end jacobi.Finite
