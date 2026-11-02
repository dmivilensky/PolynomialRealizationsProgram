import jacobi.Finite.GreenEntries
import Mathlib.Analysis.Complex.Basic

/-!
Article: jacobi, Corollary C.6.
The actual complex resolvent of a finite real symmetric matrix is
computed in the same original real orthogonal eigenbasis. This exact
identity links shifted finite spectral sums with the actual matrix
inverse, including every complex shift off the genuine finite poles.
Source: finite orthogonal spectral calculus over the complex field.
Use: finiteShiftedDiagonal_matrix identifies the actual shifted Jacobi inverse with the original finite spectral sums in Theorem C.5.
-/
namespace jacobi.Finite
noncomputable section
open Matrix chebyshev1 chebyshev2

/-- Every actual finite complex resolvent entry has its original real
spectral-vector representation whenever its genuine gaps are nonzero.
Use: finiteShiftedDiagonal_matrix identifies the actual shifted
Jacobi inverse with the original finite spectral sums in Theorem C.5.
Article: jacobi, Corollary C.6.
Proof: complexify the same original orthogonal basis. Its actual
transpose identities and diagonalization persist under the scalar
inclusion. Conjugate the genuine nonzero diagonal inverse back and
verify its left inverse before evaluating its unchanged physical entry. -/
theorem complex_resolvent_entry {N:ℕ} (J:Jacobi N) (B:SpectralBasis J.matrix)
    (z:ℂ) (hne:∀k:Fin N,z-(B.eigenvalues k:ℂ)≠0) (i j:Fin N) :
    ((z • (1:Matrix (Fin N) (Fin N) ℂ)-J.matrix.map Complex.ofRealHom)⁻¹) i j=
      ∑k:Fin N,(B.Q i k:ℂ)*(B.Q j k:ℂ)/(z-(B.eigenvalues k:ℂ)) := by
  -- The original real basis is complexified, retaining both genuine orthogonality identities.
  let Q := B.Q.map Complex.ofRealHom
  let A := z • (1:Matrix (Fin N) (Fin N) ℂ)-J.matrix.map Complex.ofRealHom
  let D := Matrix.diagonal (fun k:Fin N => z-(B.eigenvalues k:ℂ))
  have hqt : Qᵀ*Q=1 := by
    change (B.Qᵀ).map Complex.ofRealHom*B.Q.map Complex.ofRealHom=1
    rw [← Matrix.map_mul,B.transpose_mul]
    exact Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)
  have hqq : Q*Qᵀ=1 := by
    change B.Q.map Complex.ofRealHom*(B.Qᵀ).map Complex.ofRealHom=1
    rw [← Matrix.map_mul,B.mul_transpose]
    exact Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)
  have hdiag : Qᵀ*J.matrix.map Complex.ofRealHom*Q=Matrix.diagonal (fun k => (B.eigenvalues k:ℂ)) := by
    change ((B.Qᵀ).map Complex.ofRealHom*J.matrix.map Complex.ofRealHom)*B.Q.map Complex.ofRealHom=_
    rw [← Matrix.map_mul,← Matrix.map_mul,B.diagonalize,Matrix.diagonal_map (map_zero Complex.ofRealHom)]
    rfl
  have hcoord : Qᵀ*A*Q=D := by
    dsimp only [A]
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hqt,hdiag]
    ext k l
    by_cases hkl:k=l <;> simp [D,hkl]
  have hback : A=Q*D*Qᵀ := by
    rw [← hcoord]
    simp only [← Matrix.mul_assoc,hqq,Matrix.one_mul]
    rw [Matrix.mul_assoc,hqq,Matrix.mul_one]
  let R := Q*Matrix.diagonal (fun k:Fin N => (z-(B.eigenvalues k:ℂ))⁻¹)*Qᵀ
  have hRA : R*A=1 := by
    rw [hback]
    dsimp only [R]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ Q (D*Qᵀ),hqt,Matrix.one_mul,← Matrix.mul_assoc
      (Matrix.diagonal (fun k:Fin N => (z-(B.eigenvalues k:ℂ))⁻¹)) D Qᵀ]
    have hd : Matrix.diagonal (fun k:Fin N => (z-(B.eigenvalues k:ℂ))⁻¹)*D=1 := by
      simp only [D,Matrix.diagonal_mul_diagonal,inv_mul_cancel₀ (hne _),Matrix.diagonal_one]
    rw [hd,Matrix.one_mul,hqq]
  have hinv : A⁻¹=R := Matrix.inv_eq_left_inv hRA
  rw [show (z • (1:Matrix (Fin N) (Fin N) ℂ)-J.matrix.map Complex.ofRealHom)⁻¹=R from hinv]
  dsimp only [R]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,Q,Matrix.map_apply,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k _
  change (B.Q i k:ℂ)*(z-(B.eigenvalues k:ℂ))⁻¹*(B.Q j k:ℂ)=_
  ring

end
end jacobi.Finite
